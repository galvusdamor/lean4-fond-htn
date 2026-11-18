"""Shapes of two-hole plans and the width they need.  (HD2_LU.md §6.10)

A plan of the abstract model (cont = b < u < a, stop = s), read left to right, moves the pair
(depth of hole X, depth of hole Y) through the grid: an opening of a level is a step up in one
coordinate, a closing a step down.  `build(moves)` turns a move string over X, x, Y, y, S, T
(open X level, close X level, …, bottom of X, bottom of Y) into a plan and its interpretation;
`loop(out, back)` closes a path from the origin to the bottoms (`out`) with the reverse of
another one (`back`).

    python3 loops.py            # widths of the shapes of §6.10
    python3 loops.py band D K N # try N random u-placements to force a band (u's free)
"""
import random
import sys

from width import min_width, width_lb


def build(moves):
    seq, open_, pairs, bottom = [], {'X': [], 'Y': []}, {'X': [], 'Y': []}, {}
    for i, m in enumerate(moves):
        if m in 'XY':
            seq.append('b')
            open_[m].append(i)
        elif m in 'xy':
            H = m.upper()
            pairs[H].append((open_[H].pop(), i))
            seq.append('a')
        else:
            seq.append('s')
            bottom['X' if m == 'S' else 'Y'] = i
    return ''.join(seq), {H: (sorted(pairs[H]), bottom[H]) for H in 'XY'}


def loop(out, back):
    return out + 'ST' + ''.join(c.lower() for c in reversed(back))


def band(d, k):
    """Two parallel staircases at distance d with k diagonal steps between them."""
    return loop('X' * d + 'YX' * k + 'Y' * d, 'Y' * d + 'XY' * k + 'X' * d)


def shapes():
    cases = {}
    for r in (1, 2, 3):
        cases[f'{r} L-bubble(s) 2x2'] = loop('XXYY' * r, 'YYXX' * r)
    for a, b in ((3, 3), (4, 4)):
        cases[f'L-bubble {a}x{b}'] = loop('X' * a + 'Y' * b, 'Y' * b + 'X' * a)
    for d, k in ((2, 2), (3, 0), (3, 1), (3, 2), (4, 2), (5, 2)):
        cases[f'band d={d} k={k}'] = band(d, k)
    for n in (2, 3, 4):
        cases[f'triangle n={n}'] = 'X' * n + 'S' + 'Yx' * n + 'T' + 'y' * n
    for name, mv in cases.items():
        seq, lv = build(mv)
        print(f'{name:22s} {seq:36s} width {min_width(seq, lv, wmax=8)}', flush=True)


def force_band(d, k, tries, seed=0):
    """Random u-placements inside the band's own windows; least width over all interpretations."""
    rng = random.Random(seed)
    seq, lv = build(band(d, k))
    wins = [w for H in 'XY' for w in lv[H][0]]
    best = None
    for _ in range(tries):
        ins = []
        for (b, a) in wins:
            r = rng.random()
            ins.append(b + 1 if r < 0.4 else a if r < 0.8 else rng.randint(b + 1, a))
        s = list(seq)
        for p in sorted(ins, reverse=True):
            s.insert(p, 'u')
        s = ''.join(s)
        w, v = width_lb(s, wmax=5)
        if best is None or (w or 0) > (best[0] or 0):
            best = (w, v, s)
    return min_width(seq, lv), best


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == 'band':
        d, k, n = map(int, sys.argv[2:5])
        print(force_band(d, k, n))
    else:
        shapes()
