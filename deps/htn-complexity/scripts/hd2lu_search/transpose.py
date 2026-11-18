"""Local thinning by one adjacent transposition.  (HD2_LU.md §6.13)

For a pairing of width > W, try every adjacent transposition of two different labels, among
the openings or among the closings.  Keep it if the result has smaller width and Hall counts ≤
the original's in all four families (`domwidth.counts`).  A transposition of that kind makes the
thicker interpretation unnecessary for unordered floating tasks.

    python3 transpose.py N W     # all pairings of width > W on N levels (adjacent bottoms)
"""
import sys

import numpy as np

from domwidth import all_pairings, counts
from famsearch import skeleton_lv
from width import min_width

FAMS = ['oo', 'op', 'po', 'pp']


def neighbours(p):
    lo, lc = p
    out = []
    for s, which in ((lo, 0), (lc, 1)):
        for i in range(len(s) - 1):
            if s[i] != s[i + 1]:
                t = s[:i] + s[i + 1] + s[i] + s[i + 2:]
                out.append((t, lc) if which == 0 else (lo, t))
    return out


def main(N, W):
    skel = 'b' * N + 'ss' + 'a' * N
    width = lambda p: min_width(skel, skeleton_lv(N, *p), wmax=8)
    thick = [p for p in all_pairings(N)
             if min_width(skel, skeleton_lv(N, *p), wmax=W) is None]
    print(f'N={N}: {len(thick)} pairings of width > {W}', flush=True)
    fails = 0
    for p in thick:
        wp = width(p)
        cp = np.concatenate([counts([p], N, f)[0] for f in FAMS])
        good = []
        for q in neighbours(p):
            if width(q) < wp:
                cq = np.concatenate([counts([q], N, f)[0] for f in FAMS])
                if np.all(cq <= cp):
                    good.append(q)
        if not good:
            fails += 1
            print('   no thinning transposition:', p, 'width', wp, flush=True)
    print(f'N={N}: {fails} of {len(thick)} have no thinning transposition')


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
