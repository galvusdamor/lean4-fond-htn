"""How many cuts do valid two-hole plans need?  (HD2_LU.md §6.8)

Abstract model of the simplest non-trivial class: cont = b < u < a (u floats w.r.t. h), stop = s.
A plan is an event sequence over {b, a, s, u}.  An *interpretation* assigns every b, a, s to one
of the two chains (holes) X, Y — per chain: its b's, then its s, then its a's, as many a's as
b's — pairs them last-in-first-out into levels, and matches every u to a level whose window
(b, a) contains it (one u per level).

For an interpretation and a set of cut positions, the isolated multi-cut search is simulated
greedily (all its moves only enable further moves, so greedy decides).  `min_cuts(seq)` is the
least number of cuts over all interpretations, or None if the plan is invalid.
"""
import itertools
import random
import sys


def chains_assignments(seq):
    """Interpretations of the skeleton: chain labels for the b, a, s events."""
    idx = [i for i, e in enumerate(seq) if e in 'bas']
    for lab in itertools.product('XY', repeat=len(idx)):
        ok = True
        chain = {}
        for i, l in zip(idx, lab):
            chain[i] = l
        levels = {}
        for H in 'XY':
            ev = [(i, seq[i]) for i in idx if chain[i] == H]
            kinds = ''.join(e for _, e in ev)
            if kinds.count('s') != 1:
                ok = False
                break
            k = kinds.index('s')
            if set(kinds[:k]) - {'b'} or set(kinds[k + 1:]) - {'a'} or kinds[:k].count('b') != kinds[k + 1:].count('a'):
                ok = False
                break
            bs = [i for i, e in ev if e == 'b']
            as_ = [i for i, e in ev if e == 'a']
            s = [i for i, e in ev if e == 's'][0]
            n = len(bs)
            levels[H] = ([(bs[j], as_[n - 1 - j]) for j in range(n)], s)
        if ok:
            yield levels


def matchings(seq, levels):
    """All ways to match the u's to levels (one per level) inside their windows."""
    us = [i for i, e in enumerate(seq) if e == 'u']
    lv = [(H, j, w) for H in 'XY' for j, w in enumerate(levels[H][0])]
    if len(us) != len(lv):
        return
    def rec(k, used, acc):
        if k == len(us):
            yield dict(acc)
            return
        t = us[k]
        for li, (H, j, (b, a)) in enumerate(lv):
            if li not in used and b < t < a:
                acc[t] = (H, j)
                yield from rec(k + 1, used | {li}, acc)
                del acc[t]
    yield from rec(0, frozenset(), {})


def succeeds(seq, levels, match, cuts):
    """Greedy isolated multi-cut search for a fixed interpretation and cut positions."""
    n = len(seq)
    bounds = [0] + sorted(cuts) + [n]
    seg = [None] * n
    for s_i in range(len(bounds) - 1):
        for p in range(bounds[s_i], bounds[s_i + 1]):
            seg[p] = s_i
    # owner of every event: (chain, depth) ; depth = level index (0-based), s = bottom
    owner = {}
    for H in 'XY':
        lvls, s = levels[H]
        for j, (b, a) in enumerate(lvls):
            owner[b] = (H, j)
            owner[a] = (H, j)
        owner[s] = (H, len(lvls))
    for t, (H, j) in match.items():
        owner[t] = (H, j)
    created = {'X': 0, 'Y': 0}          # deepest created depth per chain (level 0 from t0)
    done = [False] * n
    fwd = [bounds[i] for i in range(len(bounds) - 1)]          # next position for F_i
    bwd = [bounds[i + 1] - 1 for i in range(len(bounds) - 1)]  # next position for B_i

    def exists(p):
        H, j = owner[p]
        return j <= created[H]

    progress = True
    while progress:
        progress = False
        for i in range(len(fwd)):
            while fwd[i] <= bwd[i] and fwd[i] < bounds[i + 1] and (done[fwd[i]] or exists(fwd[i])):
                done[fwd[i]] = True
                fwd[i] += 1
                progress = True
            while bwd[i] >= fwd[i] and bwd[i] >= bounds[i] and (done[bwd[i]] or exists(bwd[i])):
                done[bwd[i]] = True
                bwd[i] -= 1
                progress = True
        for H in 'XY':
            lvls, s = levels[H]
            j = created[H]
            if j < len(lvls):
                b, a = lvls[j]
                if done[b] and done[a]:
                    created[H] += 1
                    progress = True
    return all(done)


def min_cuts(seq, kmax=3):
    best = None
    n = len(seq)
    for levels in chains_assignments(seq):
        for match in matchings(seq, levels):
            for k in range(0, kmax + 1):
                if best is not None and k >= best:
                    break
                found = False
                for cuts in itertools.combinations(range(1, n), k):
                    if succeeds(seq, levels, match, cuts):
                        found = True
                        break
                if found:
                    best = k
                    break
    return best


def random_seq(rng, nlev):
    """A random valid-looking plan: two chains with random depths, events shuffled consistently."""
    while True:
        nx = rng.randint(0, nlev)
        ny = nlev - nx
        def chain(n):
            return ['b'] * n + ['s'] + ['a'] * n
        X, Y = chain(nx), chain(ny)
        # interleave X and Y randomly, then insert u's anywhere
        seq = []
        i = j = 0
        while i < len(X) or j < len(Y):
            if j >= len(Y) or (i < len(X) and rng.random() < 0.5):
                seq.append(X[i]); i += 1
            else:
                seq.append(Y[j]); j += 1
        for _ in range(nlev):
            seq.insert(rng.randint(1, len(seq) - 1), 'u')
        return ''.join(seq)


if __name__ == "__main__":
    nlev = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    stats = {}
    worst = []
    for _ in range(count):
        seq = random_seq(rng, nlev)
        k = min_cuts(seq)
        stats[k] = stats.get(k, 0) + 1
        if k is not None and k >= 2:
            worst.append((k, seq))
    print("levels", nlev, "distribution of minimal cuts:", stats)
    for k, s in sorted(worst, reverse=True)[:5]:
        print(k, s)
