"""A closed description of the width, for adjacent bottoms.  (HD2_LU.md §6.14)

Hole levels are created in order, so at any time the processed openings are the first `a`
X-openings and the first `b` Y-openings; likewise `a'`, `b'` for the closings.  Level `j` of a
hole exists once level `j − 1` is processed on both sides, so `a` may grow only while
`a ≤ a'`, and `a'` only while `a' ≤ a` (the same for `b`, `b'`).  The unprocessed positions
form runs; the innermost run of the openings and of the closings are joined through the middle.
So the number of open segments is `runs(lo; a, b) + runs(lc reversed; a', b') − 1`.

`formula_width(lo, lc)` is the least possible maximum of that number along a schedule.  The
claim (checked by `python3 widthformula.py N` against `width.min_width`) is that it equals the
width.
"""
import heapq
import sys

from domwidth import all_pairings
from famsearch import skeleton_lv
from width import min_width


def runs(seq, a, b):
    """Maximal runs of unprocessed positions: X beyond the a-th, Y beyond the b-th."""
    cx = cy = 0
    r, prev = 0, False
    for c in seq:
        if c == 'X':
            cx += 1
            un = cx > a
        else:
            cy += 1
            un = cy > b
        if un and not prev:
            r += 1
        prev = un
    return r


def formula_width(lo, lc):
    nX, nY = lo.count('X'), lo.count('Y')
    rb = lc[::-1]                                   # closings read from the end (outermost first)

    def cost(s):
        a, b, a2, b2 = s
        return max(1, runs(lo, a, b) + runs(rb, a2, b2) - 1)

    start = (0, 0, 0, 0)
    goal = (nX, nY, nX, nY)
    best = {start: cost(start)}
    heap = [(cost(start), start)]
    while heap:
        c, s = heapq.heappop(heap)
        if s == goal:
            return c
        if c > best.get(s, 99):
            continue
        a, b, a2, b2 = s
        nxt = []
        if a < nX and a <= a2: nxt.append((a + 1, b, a2, b2))
        if a2 < nX and a2 <= a: nxt.append((a, b, a2 + 1, b2))
        if b < nY and b <= b2: nxt.append((a, b + 1, a2, b2))
        if b2 < nY and b2 <= b: nxt.append((a, b, a2, b2 + 1))
        for t in nxt:
            ct = max(c, cost(t))
            if ct < best.get(t, 99):
                best[t] = ct
                heapq.heappush(heap, (ct, t))
    return None


if __name__ == "__main__":
    N = int(sys.argv[1])
    skel = 'b' * N + 'ss' + 'a' * N
    bad = 0
    for lo, lc in all_pairings(N):
        w1 = min_width(skel, skeleton_lv(N, lo, lc), wmax=8)
        w2 = formula_width(lo, lc)
        if w1 != w2:
            bad += 1
            if bad <= 5:
                print('  differ:', lo, lc, 'solver', w1, 'formula', w2)
    print(f'N={N}: mismatches {bad}')
