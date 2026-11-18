"""Check of the width bound proof (HD2_LU.md §6.14): at every locally minimal pairing, the
schedule that follows the openings path F has cost <= 6, because B has at most 4 runs cut off
at any point of F (and symmetrically).

    python3 followF.py N
"""
import sys
from collections import Counter

import numpy as np

from domwidth import all_pairings, counts
from transpose import neighbours
from widthformula import runs

FAMS = ['oo', 'op', 'po', 'pp']


def follow_cost(lo, lc):
    """max over the schedule along F (B-side lagging by at most one step) of the open segments."""
    rb = lc[::-1]
    a = b = 0
    worst = 1
    for c in lo:
        # F-side step, B-side lags
        if c == 'X':
            a += 1
            worst = max(worst, runs(lo, a, b) + runs(rb, a - 1, b) - 1)
        else:
            b += 1
            worst = max(worst, runs(lo, a, b) + runs(rb, a, b - 1) - 1)
        worst = max(worst, runs(lo, a, b) + runs(rb, a, b) - 1)
    return worst


def main(N):
    P = all_pairings(N)
    idx = {p: i for i, p in enumerate(P)}
    C = np.concatenate([counts(P, N, f) for f in FAMS], axis=1)
    hist = Counter()
    for i, p in enumerate(P):
        if any(np.all(C[idx[q]] <= C[i]) and np.any(C[idx[q]] < C[i]) for q in neighbours(p)):
            continue
        hist[follow_cost(*p)] += 1
    print(f'N={N}: cost of following F at locally minimal pairings: {dict(sorted(hist.items()))}')


if __name__ == "__main__":
    main(int(sys.argv[1]))
