"""Forcing thick bubbles with ordered floating types.  (HD2_LU.md §6.11)

Adjacent bottoms, N levels: start from a thick pairing (width >= 3), place the floating tasks of
`rich.CONTS[name]` inside its windows (respecting the order inside a level), and compute the least
width over all valid interpretations exactly (`rich.width_lb`).  A result >= 3 would be a plan on
which every valid interpretation has a thick bubble.

    python3 ordsearch.py NAME N TRIES SEED
"""
import itertools
import random
import sys
import time

from rich import CONTS, windows, width_lb
from famsearch import skeleton_lv
from width import min_width
name, N, tries, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
c = CONTS[name]
rng = random.Random(seed)
skel = 'b' * N + 'ss' + 'a' * N
thick = []
for nx in range(1, N):
    perms = sorted(set(itertools.permutations('X' * nx + 'Y' * (N - nx))))
    for lo in perms:
        for lc in perms:
            lv = skeleton_lv(N, lo, lc)
            if min_width(skel, lv, wmax=2) is None:
                thick.append(lv)
print(name, 'thick pairings', len(thick), flush=True)
order = sorted(c.types, key=lambda t: len(c.preds[t]))
best = 0
t0 = time.time()
for t in range(tries):
    lv = rng.choice(thick)
    placed = {}
    pos = []
    ok = True
    W = {(lvl, typ): (lo, hi) for (lvl, typ, lo, hi) in windows(skel, c, lv)}
    for (lvl, typ, lo, hi) in sorted(windows(skel, c, lv), key=lambda x: order.index(x[1])):
        lo2 = max([lo] + [placed[(lvl, p)] for p in c.preds[typ]])
        succ = [b for (a, b) in c.prec if a == typ]
        hi2 = min([hi] + [W[(lvl, b)][1] for b in succ]) - 0.01 - 0.03 * len(succ)
        if lo2 + 0.01 >= hi2:
            ok = False; break
        r = rng.random()
        p = lo2 + 0.01 if r < 0.4 else hi2 if r < 0.8 else rng.uniform(lo2 + 0.01, hi2)
        placed[(lvl, typ)] = p
        pos.append((p, typ))
    if not ok:
        continue
    w = list(skel)
    for p, typ in sorted(pos, reverse=True):
        w.insert(int(p) + 1, typ)
    w = ''.join(w)
    res = width_lb(w, c, wmax=3)
    least = res[0] if res[0] is not None else 3
    if t % 10 == 9:
        print(f'  {t + 1} placements done, best so far {best}', flush=True)
    if least > best or least >= 3:
        best = max(best, least)
        print(f'  try {t}: least width {least} (>=3 means none <=2), valid {res[1]}  {w}', flush=True)
print(name, 'best', best, 'time', round(time.time() - t0), flush=True)
