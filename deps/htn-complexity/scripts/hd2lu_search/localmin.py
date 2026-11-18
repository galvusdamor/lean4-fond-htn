"""Descent by transpositions.  (HD2_LU.md §6.14)

Call a pairing *locally minimal* if no single adjacent transposition (among the openings or
among the closings) gives Hall counts that are ≤ in all four families and smaller somewhere.
From any pairing, applying such transpositions terminates in a locally minimal one that
dominates it.  So if every locally minimal pairing has width ≤ 3, unordered floating tasks never
need width > 3.

    python3 localmin.py N        # widths of all locally minimal pairings on N levels
"""
import sys
from collections import Counter

import numpy as np

from domwidth import all_pairings, counts
from famsearch import skeleton_lv
from transpose import neighbours
from width import min_width

FAMS = ['oo', 'op', 'po', 'pp']


def main(N):
    P = all_pairings(N)
    index = {p: i for i, p in enumerate(P)}
    C = np.concatenate([counts(P, N, f) for f in FAMS], axis=1)
    skel = 'b' * N + 'ss' + 'a' * N
    minimal = []
    for i, p in enumerate(P):
        better = False
        for q in neighbours(p):
            j = index[q]
            if np.all(C[j] <= C[i]) and np.any(C[j] < C[i]):
                better = True
                break
        if not better:
            minimal.append(p)
    widths = Counter()
    worst = []
    for p in minimal:
        w = min_width(skel, skeleton_lv(N, *p), wmax=8)
        widths[w] += 1
        if w >= 4:
            worst.append(p)
    print(f'N={N}: {len(P)} pairings, {len(minimal)} locally minimal, widths {dict(widths)}', flush=True)
    for p in worst[:5]:
        print('   width >= 4:', p)


if __name__ == "__main__":
    main(int(sys.argv[1]))
