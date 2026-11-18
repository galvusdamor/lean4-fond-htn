"""Descent with pins.  (HD2_LU.md §6.14)

Pins are tasks of the initial network ordered before `c₁`/`c₂` (the hole starts after them) or
after (the hole ends before them).  With adjacent bottoms, a pin for hole H is given by
`start[H]`, the number of openings before H's start, and `end[H]`, the number of closings (in
time order) after which H has ended.  Pairings must respect them: H opens nothing among the
first start[H] openings and closes nothing after closing end[H].

Interval endpoints are the hole starts and openings (start side) and the closings and hole ends
(end side).  A parent-anchored window of level 1 starts at its hole's start and ends at its
hole's end.  The script lists the widths of the locally minimal pin-respecting pairings for all
pin positions, as in `localmin.py`.

    python3 pinmin.py N [SX,SY,EX,EY ...]   # default: starts 0..2, ends N-2..N
"""
import itertools
import sys
from collections import Counter

import numpy as np

from domwidth import all_pairings
from famsearch import skeleton_lv
from transpose import neighbours
from width import min_width

FAMS = ['oo', 'op', 'po', 'pp']


def respects(p, start, end):
    lo, lc = p
    N = len(lo)
    for H in 'XY':
        if H in lo[:start[H]]:
            return False
        if H in lc[end[H]:]:
            return False
    return True


def count_vector(p, start, end):
    """Number of windows inside every interval [start point, end point], for all four families.
    Start points: 'hole start of X', 'hole start of Y', and after opening i (i = 1..N), as
    positions on a line; end points likewise."""
    lo, lc = p
    N = len(lo)
    # positions: hole start of H at start[H] - 0.5, opening i at i (1-based); closings at N + 1 + j,
    # hole end of H at N + 1 + end[H] + 0.5
    hs = {H: start[H] + 0.5 for H in 'XY'}
    he = {H: N + 1 + end[H] + 0.5 for H in 'XY'}
    S = sorted(set([hs['X'], hs['Y']] + list(range(1, N + 1))))
    E = sorted(set([he['X'], he['Y']] + [N + 1 + j for j in range(1, N + 1)]))
    out = []
    for fam in FAMS:
        st, en = [], []
        for H in 'XY':
            ops = [i + 1 for i in range(N) if lo[i] == H]
            cls = [N + 1 + j + 1 for j in range(N) if lc[j] == H]
            lv = list(zip(ops, reversed(cls)))
            for l, (o, c) in enumerate(lv):
                st.append(o if fam[0] == 'o' else (lv[l - 1][0] if l else hs[H]))
                en.append(c if fam[1] == 'o' else (lv[l - 1][1] if l else he[H]))
        st, en = np.array(st), np.array(en)
        inside = (st[None, None, :] >= np.array(S)[:, None, None]) & \
                 (en[None, None, :] <= np.array(E)[None, :, None])
        out.append(inside.sum(axis=2).ravel())
    return np.concatenate(out)


def main(N):
    P = all_pairings(N)
    skel = 'b' * N + 'ss' + 'a' * N
    width_cache = {}
    overall = Counter()
    configs = (itertools.product(range(0, 3), range(0, 3), range(N - 2, N + 1), range(N - 2, N + 1))
               if len(sys.argv) < 3 else [tuple(int(v) for v in c.split(',')) for c in sys.argv[2:]])
    for sx, sy, ex, ey in configs:
        start, end = {'X': sx, 'Y': sy}, {'X': ex, 'Y': ey}
        Q = [p for p in P if respects(p, start, end)]
        if not Q:
            continue
        index = {p: i for i, p in enumerate(Q)}
        C = np.array([count_vector(p, start, end) for p in Q])
        widths = Counter()
        for i, p in enumerate(Q):
            better = False
            for q in neighbours(p):
                j = index.get(q)
                if j is not None and np.all(C[j] <= C[i]) and np.any(C[j] < C[i]):
                    better = True
                    break
            if not better:
                if p not in width_cache:
                    width_cache[p] = min_width(skel, skeleton_lv(N, *p), wmax=8)
                widths[width_cache[p]] += 1
        overall.update(widths)
        if max(widths) >= 4:
            print(f'  pins start={start} end={end}: locally minimal widths {dict(widths)}', flush=True)
    print(f'N={N}: widths of locally minimal pairings over all pin positions {dict(overall)}')


if __name__ == "__main__":
    main(int(sys.argv[1]))
