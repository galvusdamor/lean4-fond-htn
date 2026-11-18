"""Can ordered floating tasks force more width than unordered ones?  (HD2_LU.md §6.13)

Bottoms adjacent, N levels.  The floating types and their in-level order are given by a
`rich.Cont`.  Starting from a pairing of width > W, place every type's task of every level
inside that pairing's windows (respecting the in-level order), then minimise the number of
pairings of width ≤ W that stay valid.

* Necessary filter: for each type separately, Glover's condition on its Hall counts.
* Exact check of the survivors: `rich.valid`.

    python3 chainforce.py CONT N W RESTARTS STEPS SEED
"""
import random
import sys

import numpy as np

from domwidth import all_pairings, counts
from famsearch import skeleton_lv
from rich import CONTS, Cont, windows
from cvalid import cvalid as valid
from width import min_width

EXTRA = {
    # the four unordered anchorings plus a chain u ≺ v from own b to own a
    'four+chain': Cont({'p': (True, True), 'q': (True, False), 'r': (False, True), 's2': (False, False),
                        'u': (True, False), 'v': (False, True)}, {('u', 'v')}),
    'chain3': Cont({'u': (True, False), 'v': (False, False), 'w': (False, True)},
                   {('u', 'v'), ('v', 'w'), ('u', 'w')}),
    'two chains': Cont({'u': (True, False), 'v': (False, True), 'w': (False, True), 'z': (True, False)},
                       {('u', 'v'), ('w', 'z')}),
}


def fam_of(t, cont):
    ab, ba = cont.types[t]
    return ('o' if ab else 'p') + ('o' if ba else 'p')


def main(cname, N, W, restarts, steps, seed):
    cont = CONTS.get(cname) or EXTRA[cname]
    letters = {t: (t if len(t) == 1 else 'k') for t in cont.types}
    assert len(set(letters.values())) == len(letters)
    lc = Cont({letters[t]: v for t, v in cont.types.items()},
              {(letters[a], letters[b]) for a, b in cont.prec})
    rng = random.Random(seed)
    skel = 'b' * N + 'ss' + 'a' * N
    P = all_pairings(N)
    wid = np.array([min_width(skel, skeleton_lv(N, *p), wmax=W) is not None for p in P])
    thin = np.where(wid)[0]
    thick = np.where(~wid)[0]
    fams = sorted({fam_of(t, lc) for t in lc.types})
    C = {f: counts(P, N, f) for f in fams}
    print(f'{cname}: N={N}, {len(thick)} pairings of width > {W}', flush=True)

    def lv_in_word(word, p):
        bs = [i for i, e in enumerate(word) if e == 'b']
        as_ = [i for i, e in enumerate(word) if e == 'a']
        ss = [i for i, e in enumerate(word) if e == 's']
        lv = {}
        for k, H in enumerate('XY'):
            ops = [bs[i] for i in range(N) if p[0][i] == H]
            cls = [as_[j] for j in range(N) if p[1][j] == H]
            lv[H] = (sorted(zip(ops, reversed(cls))), ss[k])
        return lv

    def ucounts(word, t):
        """Task counts of type t for every interval (k, m), as in domwidth.counts."""
        bs = [i for i, e in enumerate(word) if e == 'b']
        as_ = [i for i, e in enumerate(word) if e == 'a']
        pos = [i for i, e in enumerate(word) if e == t]
        out = []
        for k in range(1, N + 2):
            lo = bs[N - k] if k <= N else -1
            for m in range(1, N + 2):
                hi = as_[m - 1] if m <= N else len(word)
                out.append(sum(1 for x in pos if lo < x < hi))
        return np.array(out, dtype=np.int16)

    def n_valid_thin(word):
        ok = np.ones(len(P), dtype=bool)
        for t in lc.types:
            ok &= np.all(C[fam_of(t, lc)] <= ucounts(word, t), axis=1)
        cand = [i for i in thin if ok[i]]

        def ok_exact(i):
            try:
                return valid(word, lc, lv_in_word(word, P[i]))
            except RuntimeError:
                return True                     # undecided within budget: count as valid
        return sum(1 for i in cand if ok_exact(i)), len(cand)

    def build(src, keys):
        """Word for the skeleton with floating tasks at fractional positions keys[(level, type)]."""
        pos = sorted((x, t) for (lvl, t), x in keys.items())
        w = list(skel)
        for x, t in reversed(pos):
            w.insert(int(x) + 1, t)
        return ''.join(w)

    order = sorted(lc.types, key=lambda t: len(lc.preds[t]))
    best = None
    for r in range(restarts):
        src = P[rng.choice(thick)]
        lv = skeleton_lv(N, *src)
        win = {(lvl, t): (lo, hi) for (lvl, t, lo, hi) in windows(skel, lc, lv)}

        def sample(keys, key):
            lvl, t = key
            lo, hi = win[key]
            lo2 = max([lo] + [keys[(lvl, p)] for p in lc.preds[t] if (lvl, p) in keys])
            succ = [b for (a, b) in lc.prec if a == t]
            hi2 = min([hi] + [win[(lvl, b)][1] for b in succ]) - 0.01 - 0.03 * len(succ)
            hi2 = min([hi2] + [keys[(lvl, b)] - 0.001 for b in succ if (lvl, b) in keys])
            return None if lo2 + 0.01 >= hi2 else rng.uniform(lo2 + 0.01, hi2)

        keys = {}
        for key in sorted(win, key=lambda k: order.index(k[1])):
            x = sample(keys, key)
            if x is None:
                break
            keys[key] = x
        if len(keys) < len(win):
            continue
        cur = n_valid_thin(build(src, keys))
        for _ in range(steps):
            key = rng.choice(list(keys))
            old = keys.pop(key)
            x = sample(keys, key)
            if x is None:
                keys[key] = old
                continue
            keys[key] = x
            new = n_valid_thin(build(src, keys))
            if new[0] <= cur[0]:
                cur = new
            else:
                keys[key] = old
            if cur[0] == 0:
                break
        if best is None or cur[0] < best[0]:
            best = (cur[0], build(src, keys), src)
            print(f'  restart {r}: thin valid {cur[0]} (count filter passed {cur[1]}), source {src}, '
                  f'plan {best[1]}', flush=True)
        if best[0] == 0:
            break
    print('best', best)


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]),
         int(sys.argv[6]))
