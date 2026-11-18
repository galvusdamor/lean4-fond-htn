/* Exact matcher for floating tasks (HD2_LU.md §6.13), the C version of rich.valid.
 *
 * Slots: one per (level, floating type), with an open window (lo, hi), a type, and a bit mask
 * of the slots of the same level that must be filled earlier (in-level order).  Executions:
 * positions (increasing) and types.  Executions are assigned in time order; a slot whose
 * window has passed unfilled is a failure.  Failed states (k, filled) are memoised.
 *
 * Build: cc -O2 -shared -fPIC -o cmatch.so cmatch.c
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define TABLE (1 << 20)

static uint64_t *keys_mask;
static int32_t *keys_k;
static uint32_t *keys_gen;
static uint32_t gen;
static long stored;

static int seen(int k, uint64_t mask) {
    uint64_t h = (mask * 0x9E3779B97F4A7C15ULL) ^ ((uint64_t)k * 0xC2B2AE3D27D4EB4FULL);
    uint32_t i = (uint32_t)(h >> 40) & (TABLE - 1);
    while (keys_gen[i] == gen) {
        if (keys_k[i] == k && keys_mask[i] == mask) return 1;
        i = (i + 1) & (TABLE - 1);
    }
    return 0;
}

static void remember(int k, uint64_t mask) {
    if (stored > TABLE / 2) return;                 /* table full enough: stop memoising */
    uint64_t h = (mask * 0x9E3779B97F4A7C15ULL) ^ ((uint64_t)k * 0xC2B2AE3D27D4EB4FULL);
    uint32_t i = (uint32_t)(h >> 40) & (TABLE - 1);
    while (keys_gen[i] == gen) i = (i + 1) & (TABLE - 1);
    keys_gen[i] = gen;
    keys_k[i] = k;
    keys_mask[i] = mask;
    stored++;
}

static int ns, nx;
static const int *slo, *shi, *styp;
static const uint64_t *spred;
static const int *xpos, *xtyp;
static long budget;

static int rec(int k, uint64_t filled) {
    if (k == nx) return 1;
    if (--budget < 0) return 0;
    if (seen(k, filled)) return 0;
    int t = xpos[k], ty = xtyp[k];
    for (int s = 0; s < ns; s++)
        if (!(filled >> s & 1) && shi[s] <= t) { remember(k, filled); return 0; }
    for (int s = 0; s < ns; s++) {
        if (styp[s] != ty || (filled >> s & 1) || !(slo[s] < t && t < shi[s])) continue;
        if ((spred[s] & filled) != spred[s]) continue;
        /* skip a slot interchangeable with an earlier candidate */
        int dup = 0;
        for (int r = 0; r < s; r++)
            if (styp[r] == ty && !(filled >> r & 1) && slo[r] == slo[s] && shi[r] == shi[s]
                && spred[r] == 0 && spred[s] == 0 && slo[r] < t && t < shi[r]) { dup = 1; break; }
        if (dup) continue;
        if (rec(k + 1, filled | (1ULL << s))) return 1;
    }
    remember(k, filled);
    return 0;
}

/* returns 1 valid, 0 invalid, -1 budget exhausted */
int valid(int n_slots, const int *lo, const int *hi, const int *typ, const uint64_t *pred,
          int n_ex, const int *pos, const int *xt, long max_steps) {
    if (n_slots > 64 || n_slots != n_ex) return n_slots == n_ex ? -1 : 0;
    if (!keys_k) {
        keys_k = malloc(sizeof(int32_t) * TABLE);
        keys_mask = malloc(sizeof(uint64_t) * TABLE);
        keys_gen = calloc(TABLE, sizeof(uint32_t));
    }
    gen++;
    stored = 0;
    ns = n_slots; nx = n_ex; slo = lo; shi = hi; styp = typ; spred = pred; xpos = pos; xtyp = xt;
    budget = max_steps;
    int r = rec(0, 0);
    return budget < 0 ? -1 : r;
}
