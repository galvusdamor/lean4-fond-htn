"""Can event sequences force many cuts?  (HD2_LU.md §6.9)

Class: cont = b < u < a, stop = s; each level needs one u inside its window (b, a).
For an event sequence over {b, a, s, u}:

* `interpretations(seq)` enumerates the ways to split the b/a/s events into two chains
  (b's, then s, then as many a's; levels paired last-in-first-out);
* `hall_ok` checks, by earliest-deadline-first matching (exact for one task type), that the u's
  can be matched to the levels inside their windows;
* `cuts_lb(seq)` is the least number of cuts over all valid interpretations for the isolated
  multi-cut search **with u's never blocking** — a lower bound on the true minimum.
"""
import itertools
import sys


def interpretations(seq):
    """DFS over the b/a/s events; chain state: (phase, open-level stack)."""
    events = [(i, e) for i, e in enumerate(seq) if e in 'bas']
    out = []

    def rec(k, st, levels):
        if k == len(events):
            if all(st[H][0] == 'asc' and not st[H][1] for H in 'XY'):
                out.append({H: (list(levels[H][0]), levels[H][1]) for H in 'XY'})
            return
        i, e = events[k]
        for H in 'XY':
            phase, stack = st[H]
            if e == 'b' and phase == 'desc':
                nst = dict(st); nst[H] = (phase, stack + (i,))
                rec(k + 1, nst, levels)
            elif e == 's' and phase == 'desc':
                nst = dict(st); nst[H] = ('asc', stack)
                nl = dict(levels); nl[H] = (levels[H][0], i)
                rec(k + 1, nst, nl)
            elif e == 'a' and phase == 'asc' and stack:
                b = stack[-1]
                nst = dict(st); nst[H] = (phase, stack[:-1])
                nl = dict(levels); nl[H] = (levels[H][0] + ((b, i),), levels[H][1])
                rec(k + 1, nst, nl)
            if H == 'X' and st['X'] == st['Y'] and levels['X'] == levels['Y']:
                break   # the two chains are still symmetric: one choice suffices

    rec(0, {'X': ('desc', ()), 'Y': ('desc', ())}, {'X': ((), None), 'Y': ((), None)})
    # levels per chain must be ordered by depth: the pairs were appended in closing order
    res = []
    for lv in out:
        r = {}
        for H in 'XY':
            pairs, s = lv[H]
            pairs = sorted(pairs)            # by opening time = by depth
            r[H] = (pairs, s)
        res.append(r)
    return res


def hall_ok(seq, lv):
    us = [i for i, e in enumerate(seq) if e == 'u']
    wins = [w for H in 'XY' for w in lv[H][0]]
    if len(us) != len(wins):
        return False
    pending = []
    used = [False] * len(wins)
    for t in us:
        cand = [k for k, (b, a) in enumerate(wins) if not used[k] and b < t < a]
        if not cand:
            return False
        k = min(cand, key=lambda k: wins[k][1])
        used[k] = True
    # deadlines: every level must have got a u (counts are equal, so all used)
    return all(used)


def succeeds(seq, lv, cuts):
    n = len(seq)
    bounds = [0] + sorted(cuts) + [n]
    owner = {}
    for H in 'XY':
        pairs, s = lv[H]
        for j, (b, a) in enumerate(pairs):
            owner[b] = (H, j); owner[a] = (H, j)
        owner[s] = (H, len(pairs))
    created = {'X': 0, 'Y': 0}
    done = [False] * n
    S = len(bounds) - 1
    fwd = [bounds[i] for i in range(S)]
    bwd = [bounds[i + 1] - 1 for i in range(S)]

    def ok(p):
        if p not in owner:
            return True                      # u's never block (lower bound)
        H, j = owner[p]
        return j <= created[H]

    progress = True
    while progress:
        progress = False
        for i in range(S):
            while fwd[i] <= bwd[i] and ok(fwd[i]):
                done[fwd[i]] = True; fwd[i] += 1; progress = True
            while bwd[i] >= fwd[i] and ok(bwd[i]):
                done[bwd[i]] = True; bwd[i] -= 1; progress = True
        for H in 'XY':
            pairs, s = lv[H]
            j = created[H]
            if j < len(pairs) and done[pairs[j][0]] and done[pairs[j][1]]:
                created[H] += 1; progress = True
    return all(done)


def min_cuts_for(seq, lv, kmax):
    for k in range(kmax + 1):
        for cuts in itertools.combinations(range(1, len(seq)), k):
            if succeeds(seq, lv, cuts):
                return k
    return None


def cuts_lb(seq, kmax=4):
    best = None
    valid = 0
    for lv in interpretations(seq):
        if not hall_ok(seq, lv):
            continue
        valid += 1
        k = min_cuts_for(seq, lv, kmax if best is None else best - 1)
        if k is not None and (best is None or k < best):
            best = k
            if best == 0:
                break
    return best, valid


if __name__ == "__main__":
    for seq in sys.argv[1:]:
        print(seq, cuts_lb(seq))
