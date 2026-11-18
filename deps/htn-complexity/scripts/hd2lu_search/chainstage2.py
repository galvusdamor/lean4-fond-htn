"""Two-stage forcing: unordered tasks first, then a chain.  (HD2_LU.md §6.13)

Stage 1 (`forcethick.py`) places the four unordered types so that few thin pairings stay valid.
Adding further floating tasks can only remove valid pairings.  Stage 2 adds the tasks of an
ordered pair `c ≺ d` (anchorings given) inside the source pairing's windows.  It hill-climbs
their positions to make the remaining thin pairings invalid, checked exactly with the C matcher.

    python3 chainstage2.py N W SOURCE_LO SOURCE_LC 'PLACEMENT' CHAINS RESTARTS STEPS SEED

PLACEMENT is the dictionary printed by forcethick.py; CHAINS lists ordered pairs of anchorings
('oo', 'op', 'po', 'pp'), e.g. 'op:op,pp:pp' for two chains c ≺ d and e ≺ f.
"""
import ast
import random
import sys

from cvalid import cvalid
from domwidth import all_pairings
from famsearch import gaps, skeleton_lv
from rich import Cont, windows
from width import min_width

LETTER = {'oo': 'u', 'op': 'v', 'po': 'w', 'pp': 'z'}


CHAIN_LETTERS = [('c', 'd'), ('e', 'f'), ('g', 'h'), ('i', 'j')]


def main(N, W, src, place, chains, restarts, steps, seed):
    rng = random.Random(seed)
    G = gaps(N)
    ng = len(G)
    flag = lambda f: (f[0] == 'o', f[1] == 'o')
    ctypes_, prec = {}, set()
    for (ca, da), (c1, c2) in zip(chains, CHAIN_LETTERS):
        ctypes_[c1], ctypes_[c2] = flag(ca), flag(da)
        prec.add((c1, c2))
    pairs = [(c1, c2) for (_, _), (c1, c2) in zip(chains, CHAIN_LETTERS)]
    cont = Cont({**{LETTER[f]: flag(f) for f in LETTER}, **ctypes_}, prec)
    skel = 'b' * N + 'ss' + 'a' * N
    # skeleton positions of the gaps: a task in gap g sits right after skeleton position gpos[g]
    gpos = [-1] + list(range(N)) + [N + 1 + j for j in range(1, N)] + [2 * N + 1]
    base = [(gpos[g] + 0.5, LETTER[f]) for f, gl in place.items() for g in gl]
    lv0 = skeleton_lv(N, *src)
    win = {(lvl, t): (lo, hi) for (lvl, t, lo, hi) in windows(skel, cont, lv0) if t in ctypes_}

    def word(extra):
        items = sorted(base + extra)
        w = list(skel)
        for x, t in reversed(items):
            w.insert(int(x) + 1, t)
        return ''.join(w)

    def lv_in(word, p):
        bs = [i for i, e in enumerate(word) if e == 'b']
        as_ = [i for i, e in enumerate(word) if e == 'a']
        ss = [i for i, e in enumerate(word) if e == 's']
        return {H: (sorted(zip([bs[i] for i in range(N) if p[0][i] == H],
                               reversed([as_[j] for j in range(N) if p[1][j] == H]))), ss[k])
                for k, H in enumerate('XY')}

    # thin pairings valid for the unordered types alone (stage 1)
    w0 = word([])
    u_cont = Cont({LETTER[f]: flag(f) for f in LETTER})
    P = all_pairings(N)
    thin = [p for p in P if min_width(skel, skeleton_lv(N, *p), wmax=W) is not None]
    alive = [p for p in thin if cvalid(w0, u_cont, lv_in(w0, p))]
    print(f'stage 1 leaves {len(alive)} thin pairings valid; chains {chains}', flush=True)

    def score(extra):
        w = word(extra)
        assert cvalid(w, cont, lv_in(w, src)), 'source must stay valid'
        n = 0
        for p in alive:
            try:
                n += cvalid(w, cont, lv_in(w, p))
            except RuntimeError:
                n += 1
        return n

    levels = sorted({lvl for (lvl, t) in win})

    def sample(lvl, c1, c2):
        lo_c, hi_c = win[(lvl, c1)]
        lo_d, hi_d = win[(lvl, c2)]
        x = rng.uniform(lo_c + 0.01, min(hi_c, hi_d) - 0.02)
        y = rng.uniform(max(lo_d, x) + 0.005, hi_d - 0.005)
        return x, y

    best = None
    for r in range(restarts):
        pos = {(lvl, k): sample(lvl, *pairs[k]) for lvl in levels for k in range(len(pairs))}
        extra = lambda: [(x, pairs[k][0]) for (lvl, k), (x, y) in pos.items()] + \
                        [(y, pairs[k][1]) for (lvl, k), (x, y) in pos.items()]
        cur = score(extra())
        for _ in range(steps):
            key = rng.choice(list(pos))
            old = pos[key]
            pos[key] = sample(key[0], *pairs[key[1]])
            new = score(extra())
            if new <= cur:
                cur = new
            else:
                pos[key] = old
            if cur == 0:
                break
        if best is None or cur < best[0]:
            best = (cur, word(extra()))
            print(f'  restart {r}: thin valid {cur}  plan {best[1]}', flush=True)
        if best[0] == 0:
            break
    print('best', best)


if __name__ == "__main__":
    a = sys.argv
    chains = [tuple(c.split(':')) for c in a[6].split(',')]
    main(int(a[1]), int(a[2]), (a[3], a[4]), ast.literal_eval(a[5]), chains, int(a[7]), int(a[8]),
         int(a[9]))
