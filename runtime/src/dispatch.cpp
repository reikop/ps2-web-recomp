#include "ps2/generated.hpp"
#include "ps2/system.hpp"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <set>
#include <string>
#include <vector>

namespace ps2 {

namespace {

std::vector<UnitInfo> g_units;
std::vector<const UnitInfo *> g_index;
std::uint32_t g_origin = 0;
std::uint32_t g_unit_size = 1;
std::set<std::uint32_t> g_misses;
std::set<std::string> g_module_misses;

constexpr std::uint32_t kModuleMagic = 0x32524E53u;

struct Instance {
    std::uint32_t base;
    const ModuleInfo *module;
};

const ModuleInfo *g_modules = nullptr;
std::uint32_t g_module_count = 0;
std::uint32_t g_module_span = 0;
std::vector<Instance> g_instances;
constexpr std::size_t kMaxInstances = 64;

bool loaded_at(const ModuleInfo &m, std::uint32_t base) {
    if (m.fixed_base) {
        if (base != m.fixed_base) return false;
    } else if (ld32(base + 0x2Cu) != m.size) {
        return false;
    }
    for (std::uint32_t k = 0; k < m.check_count; ++k)
        if (ld32(base + m.checks[2 * k]) != m.checks[2 * k + 1]) return false;
    return true;
}

std::uint32_t g_spot_cursor = 0;

// Window images are translated so that control leaves a unit only through
// dispatch, so an image serves a pc as long as the code words of the unit
// holding it are in place: a game that keeps code and data side by side in a
// window rewrites other parts freely. Window checks are sorted by offset.
constexpr std::uint32_t kNearChecks = 8;

std::uint32_t first_check(const ModuleInfo &m, std::uint32_t offset) {
    std::uint32_t lo = 0, hi = m.check_count;
    while (lo < hi) {
        const std::uint32_t mid = (lo + hi) / 2;
        if (m.checks[2 * mid] < offset) lo = mid + 1;
        else hi = mid;
    }
    return lo;
}

const UnitInfo *module_unit(const ModuleInfo &m, std::uint32_t offset);

// the checks of the unit holding offset, and the word a delay slot may read past it
void unit_checks(const ModuleInfo &m, std::uint32_t offset, std::uint32_t &from, std::uint32_t &to) {
    const UnitInfo *u = module_unit(m, offset);
    if (!u) {
        from = to = 0;
        return;
    }
    from = first_check(m, u->base);
    to = first_check(m, u->base + u->size + 4u);
}

bool unit_in_place(const ModuleInfo &m, std::uint32_t pc) {
    std::uint32_t from, to;
    unit_checks(m, pc - m.fixed_base, from, to);
    if (from == to) return false;
    for (std::uint32_t k = from; k < to; ++k)
        if (ld32(m.fixed_base + m.checks[2 * k]) != m.checks[2 * k + 1]) return false;
    return true;
}

// The word a call checks turns with each call over the unit, so every code
// word of it is proven again within its check count calls, and the code words
// around the pc are proven every time.
bool near_in_place(const Instance &i, std::uint32_t pc) {
    const ModuleInfo &m = *i.module;
    std::uint32_t from, to;
    unit_checks(m, pc - i.base, from, to);
    if (from == to) return false;
    const std::uint32_t c = from + g_spot_cursor++ % (to - from);
    if (ld32(i.base + m.checks[2 * c]) != m.checks[2 * c + 1]) return false;
    const std::uint32_t at = first_check(m, pc - i.base);
    const std::uint32_t lo = std::max(from, at > kNearChecks / 2 ? at - kNearChecks / 2 : 0u);
    const std::uint32_t hi = std::min(to, at + kNearChecks);
    for (std::uint32_t k = lo; k < hi; ++k)
        if (ld32(i.base + m.checks[2 * k]) != m.checks[2 * k + 1]) return false;
    return true;
}

const Instance *in_place(const Instance &i, std::uint32_t pc) {
    static const bool full = std::getenv("PS2_WINDOW_FULL") != nullptr;
    if (!i.module->fixed_base) return loaded_at(*i.module, i.base) ? &i : nullptr;
    if (full) return unit_in_place(*i.module, pc) ? &i : nullptr;
    if (!i.module->check_count) return &i;
    return near_in_place(i, pc) ? &i : nullptr;
}

Instance make_instance(std::uint32_t base, const ModuleInfo *m) {
    return {base, m};
}

const Instance *instance_for(std::uint32_t pc);

bool proven(const Instance &i, std::uint32_t pc) {
    return i.module->fixed_base ? unit_in_place(*i.module, pc) : loaded_at(*i.module, i.base);
}

// The spot check lets a cached image serve a window a game has partly
// rewritten since, as long as the word checked this call is unchanged. Before
// a pc counts as missing from that image, every check word of its unit is
// proven: a stale image drops out and the one now in place, if any, is looked
// up instead.
const Instance *proven_instance_for(std::uint32_t pc) {
    const Instance *i = instance_for(pc);
    if (!i || proven(*i, pc)) return i;
    for (std::size_t k = 0; k < g_instances.size(); ++k)
        if (&g_instances[k] == i) {
            g_instances.erase(g_instances.begin() + static_cast<std::ptrdiff_t>(k));
            break;
        }
    i = instance_for(pc);
    return i && proven(*i, pc) ? i : nullptr;
}

const Instance *instance_for(std::uint32_t pc) {
    for (std::size_t k = 0; k < g_instances.size(); ++k) {
        const Instance &i = g_instances[k];
        if (pc - i.base >= i.module->size) continue;
        if (in_place(i, pc)) return &i;
        // an image of a window may still serve its other units
        if (i.module->fixed_base) continue;
        g_instances.erase(g_instances.begin() + static_cast<std::ptrdiff_t>(k));
        break;
    }
    if (g_instances.size() > kMaxInstances) g_instances.resize(kMaxInstances / 2);
    if (!g_module_count || pc >= kRamSize) return nullptr;
    // A code window rewritten by the game holds fixed base modules, each an
    // image of one content. One whose unit at the pc is in place serves it.
    for (std::uint32_t k = 0; k < g_module_count; ++k) {
        const ModuleInfo &m = g_modules[k];
        if (m.fixed_base && pc - m.fixed_base < m.size && unit_in_place(m, pc)) {
            g_instances.push_back(make_instance(m.fixed_base, &m));
            return &g_instances.back();
        }
    }
    for (std::uint32_t at = pc & ~15u; pc - at < g_module_span; at -= 16) {
        if (ld32(at) == kModuleMagic) {
            for (std::uint32_t k = 0; k < g_module_count; ++k)
                if (pc - at < g_modules[k].size && loaded_at(g_modules[k], at)) {
                    g_instances.push_back(make_instance(at, &g_modules[k]));
                    return &g_instances.back();
                }
            return nullptr;
        }
        if (at < 16) break;
    }
    return nullptr;
}

const UnitInfo *module_unit(const ModuleInfo &m, std::uint32_t offset) {
    for (std::uint32_t k = 0; k < m.count; ++k)
        if (offset - m.units[k].base < m.units[k].size) return &m.units[k];
    return nullptr;
}

const UnitInfo *unit_for(std::uint32_t pc) {
    const std::uint32_t slot = (pc - g_origin) / g_unit_size;
    if (pc < g_origin || slot >= g_index.size()) return nullptr;
    return g_index[slot];
}

// Several images of a window may hold the code at the pc, and only some of
// them may have been translated with this pc as an entry: any of those will
// do, since every code word of its unit matches.
const Instance *instance_with_entry(std::uint32_t pc) {
    for (std::uint32_t k = 0; k < g_module_count; ++k) {
        const ModuleInfo &m = g_modules[k];
        if (!m.fixed_base || pc - m.fixed_base >= m.size) continue;
        const UnitInfo *mu = module_unit(m, pc - m.fixed_base);
        if (!mu || !mu->entries[(pc - m.fixed_base - mu->base) >> 2] || !unit_in_place(m, pc)) continue;
        g_instances.insert(g_instances.begin(), make_instance(m.fixed_base, &m));
        return &g_instances.front();
    }
    return nullptr;
}

void record_miss(std::uint32_t pc) {
    // In a fixed window several images may be in place at once, so the pc is
    // recorded bare: the capture names it after the image the RAM dump holds.
    if (const Instance *m = proven_instance_for(pc); m && !m->module->fixed_base) {
        char token[96];
        std::snprintf(token, sizeof token, "%s:%x", m->module->name, pc - m->base);
        if (!g_module_misses.insert(token).second || g_options.misses_path.empty()) return;
        std::ofstream(g_options.misses_path, std::ios::app) << token << "\n";
        return;
    }
    if (!g_misses.insert(pc).second || g_options.misses_path.empty()) return;
    std::ofstream out(g_options.misses_path, std::ios::app);
    out << std::hex << pc << "\n";
}

}

void register_units(const UnitInfo *units, std::uint32_t count) {
    g_units.assign(units, units + count);
    if (g_units.empty()) return;
    std::sort(g_units.begin(), g_units.end(), [](const UnitInfo &a, const UnitInfo &b) { return a.base < b.base; });
    g_origin = g_units.front().base;
    g_unit_size = g_units.front().size;
    g_index.assign((g_units.back().base - g_origin) / g_unit_size + 1, nullptr);
    for (const UnitInfo &u : g_units) g_index[(u.base - g_origin) / g_unit_size] = &u;
}

void register_modules(const ModuleInfo *modules, std::uint32_t count) {
    g_modules = modules;
    g_module_count = count;
    g_instances.clear();
    for (std::uint32_t k = 0; k < count; ++k) g_module_span = std::max(g_module_span, modules[k].size);
}

bool has_code(std::uint32_t pc) {
    const UnitInfo *u = unit_for(pc);
    if (u && u->entries[(pc - u->base) >> 2] != 0) return true;
    const Instance *m = instance_for(pc);
    const UnitInfo *mu = m ? module_unit(*m->module, pc - m->base) : nullptr;
    return mu && mu->entries[(pc - m->base - mu->base) >> 2] != 0;
}

// Code the translation lacks runs in the interpreter instead of halting: always
// in the browser, natively with PS2_INTERP (exploring runs halt to find it).
bool interpreter_on() {
#ifdef __EMSCRIPTEN__
    return true;
#else
    static const bool on = std::getenv("PS2_INTERP") != nullptr;
    return on;
#endif
}

void interpret(Cpu &c, std::uint32_t, std::uint32_t depth);

// debugging aid: PS2_INTERP_RANGE=lo,hi runs code entered there in the
// interpreter, to tell a translation bug from a runtime one
struct InterpRange {
    std::uint32_t lo = 0, hi = 0;
    InterpRange() {
        if (const char *s = std::getenv("PS2_INTERP_RANGE")) std::sscanf(s, "%x,%x", &lo, &hi);
    }
    bool has(std::uint32_t pc) const { return pc - lo < hi - lo; }
};
const InterpRange g_forced;

// whether dispatch finds translated code at the pc, for the interpreter to hand back to
bool translated(std::uint32_t pc) {
    if (g_forced.has(pc)) return false;
    if (const UnitInfo *u = unit_for(pc); u && u->entries[(pc - u->base) >> 2]) return true;
    if (const Instance *m = proven_instance_for(pc)) {
        const UnitInfo *mu = module_unit(*m->module, pc - m->base);
        if (mu && mu->entries[(pc - m->base - mu->base) >> 2]) return true;
    }
    return instance_with_entry(pc) != nullptr;
}

void dispatch(Cpu &c, std::uint32_t, std::uint32_t depth) {
    const std::uint32_t pc = c.pc;
    if (pc & kUnwind) return;
    if (pc == kHandlerReturn || pc == kIdle) return;
    if (g_forced.has(pc)) [[clang::musttail]] return interpret(c, 0u, depth);
    const UnitInfo *u = unit_for(pc);
    const std::uint16_t id = u ? u->entries[(pc - u->base) >> 2] : 0;
    if (!id) {
        const Instance *m = instance_for(pc);
        for (int attempt = 0; m && attempt < 2; ++attempt) {
            const std::uint32_t base = m->base;
            const UnitInfo *mu = module_unit(*m->module, pc - base);
            const std::uint16_t entry = mu ? mu->entries[(pc - base - mu->base) >> 2] : 0;
            if (entry) {
                c.base = base;
                [[clang::musttail]] return mu->function(c, entry, depth);
            }
            // no entry here may only mean the cached image went stale
            const ModuleInfo *was = m->module;
            m = proven_instance_for(pc);
            if (m && m->module == was && m->base == base) m = nullptr;
        }
        if (const Instance *other = instance_with_entry(pc)) {
            const UnitInfo *mu = module_unit(*other->module, pc - other->base);
            c.base = other->base;
            [[clang::musttail]] return mu->function(c, mu->entries[(pc - other->base - mu->base) >> 2], depth);
        }
        record_miss(pc);
        if (interpreter_on()) [[clang::musttail]] return interpret(c, 0u, depth);
        char reason[64];
        std::snprintf(reason, sizeof reason, "missing code at 0x%08X (ra 0x%08X)", pc, c.r[31].w[0]);
        std::fprintf(stderr, "[ee] no translated code at 0x%08X (ra 0x%08X)\n", pc, c.r[31].w[0]);
        for (int i = 1; i < 32; i += 4)
            std::fprintf(stderr, "[ee]   r%-2d %08X %08X %08X %08X\n", i, c.r[i].w[0], c.r[i + 1].w[0], c.r[i + 2].w[0], i + 3 < 32 ? c.r[i + 3].w[0] : 0u);
        halt(reason);
        c.pc = pc | kUnwind;
        return;
    }
    // a tail call: window code reaches other units through dispatch
    [[clang::musttail]] return u->function(c, id, depth);
}

void call(Cpu &c, std::uint32_t target, std::uint32_t depth) {
    c.pc = target;
    if (depth >= kMaxDepth) return;
    dispatch(c, 0, depth);
}

void bad_entry(Cpu &c, std::uint32_t unit_base) {
    std::fprintf(stderr, "[ee] bad entry into unit 0x%08X for pc 0x%08X\n", unit_base, c.pc);
    halt("bad entry");
    c.pc |= kUnwind;
}

void stop(Cpu &c, std::uint32_t pc, const char *what) {
    std::fprintf(stderr, "[ee] stopped at 0x%08X: %s\n", pc, what);
    halt(what);
    c.pc = pc | kUnwind;
}

void probe(Cpu &c, std::uint32_t pc) {
    std::fprintf(stderr, "[probe] 0x%08X a0 %08X a1 %08X a2 %08X a3 %08X ra %08X v0 %08X\n", pc, c.r[4].w[0], c.r[5].w[0], c.r[6].w[0],
                 c.r[7].w[0], c.r[31].w[0], c.r[2].w[0]);
}

void breakpoint(Cpu &c, std::uint32_t pc) {
    std::fprintf(stderr, "[ee] break at 0x%08X (ra 0x%08X)\n", pc, c.r[31].w[0]);
}

void trap(Cpu &c, std::uint32_t pc) {
    std::fprintf(stderr, "[ee] trap at 0x%08X (ra 0x%08X)\n", pc, c.r[31].w[0]);
}

}
