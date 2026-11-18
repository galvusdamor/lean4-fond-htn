"""Forced-thick plans versus STRIPS closures.  (HD2_LU.md §6.12)

Generate plans at N levels (four unordered floating types, one per anchoring) on which every
valid interpretation is thick, then enumerate the most restrictive STRIPS-like constraint
containing each plan (`rrb.closure_words`) and report the widths of its valid words.  A plan
whose closure has only thick valid words would force a thick bubble at the level of instances.

    python3 forcedmany.py SEED RESTARTS [N]
"""
import itertools
import random
import sys

import numpy as np

from famsearch import gaps, pairing_levels, window, skeleton_lv
from forcethick import fam_counts, interval_gaps
from rrb import closure_words, FOUR
from width import min_width

FAMS = ['oo', 'op', 'po', 'pp']
LETTER = {'oo': 'u', 'op': 'v', 'po': 'w', 'pp': 'z'}


def main(seed, restarts, N=7):
    skel = 'b' * N + 'ss' + 'a' * N
    P = []
    for nx in range(N + 1):
        perms = sorted(set(itertools.permutations('X' * nx + 'Y' * (N - nx))))
        P += [(''.join(lo), ''.join(lc)) for lo in perms for lc in perms]
    thin = np.array([min_width(skel, skeleton_lv(N, lo, lc), wmax=2) is not None for lo, lc in P])
    C = {f: np.array([fam_counts(lo, lc, f) for lo, lc in P], dtype=np.int16) for f in FAMS}
    IG, G = interval_gaps(N), gaps(N)
    ng = len(G)
    M = np.zeros((ng, len(IG)), dtype=np.int16)
    for j, (a, b) in enumerate(IG):
        M[a:b + 1, j] = 1
    thick = [i for i in range(len(P)) if not thin[i]]

    def nthin(place):
        ok = np.ones(len(P), dtype=bool)
        for f in FAMS:
            cnt = np.zeros(ng, dtype=np.int16)
            for g in place[f]:
                cnt[g] += 1
            ok &= np.all(C[f] <= cnt @ M, axis=1)
        return int((ok & thin).sum())

    def word(place, rng):
        buckets = {g: [] for g in range(ng)}
        for f, gl in place.items():
            for g in gl:
                buckets[g].append(LETTER[f])
        for g in buckets:
            rng.shuffle(buckets[g])         # the order inside a gap does not matter here
        cat = lambda g: ''.join(buckets[g])
        w = cat(0)
        for i in range(1, N + 1):
            w += 'b' + cat(G.index(f'L{i}'))
        w += 'ss'
        for j in range(1, N + 1):
            w += 'a' + (cat(G.index(f'R{j + 1}')) if j < N else '')
        return w + cat(ng - 1)

    rng = random.Random(seed)
    for _ in range(restarts):
        src = rng.choice(thick)
        lv = pairing_levels(*P[src])
        wins = {f: [window(N, lv, H, l, f) for H in 'XY' for l in range(len(lv[H]))] for f in FAMS}
        place = {f: [rng.randint(a, b) for (a, b) in wins[f]] for f in FAMS}
        cur = nthin(place)
        for _ in range(600):
            f = rng.choice(FAMS)
            j = rng.randrange(N)
            old = place[f][j]
            a, b = wins[f][j]
            place[f][j] = rng.randint(a, b)
            new = nthin(place)
            if new <= cur:
                cur = new
            else:
                place[f][j] = old
            if cur == 0:
                break
        if cur:
            continue
        w = word(place, rng)
        res = closure_words(w, FOUR, N, maxlen=len(w) + 2)
        print('forced plan', w, '| valid words in its closure', len(res),
              'widths', sorted(set(x[0] for x in res)), flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 7)
