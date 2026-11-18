"""Local search for a plan whose valid interpretations are all thick.  (HD2_LU.md §6.11)

Bottoms adjacent, N levels, one unordered floating type per family in FAMS (`famsearch.py`).
Start from a thick pairing P and place each type's tasks inside P's windows (so P stays valid).
A pairing Q is valid iff for every type its Hall counts are ≤ the task counts of every interval
(Glover; exact for one unordered type).  Hill climbing moves single tasks inside their windows
and minimises the number of *thin* (width ≤ 2) pairings that stay valid.  Zero means every valid
interpretation of the plan is thick.

    python3 forcethick.py N FAMS RESTARTS STEPS SEED [W]   # W: 'thin' means width <= W
"""
import itertools
import random
import sys

import numpy as np

from famsearch import gaps, pairing_levels, window, skeleton_lv
from width import min_width


def fam_counts(lo, lc, fam):
    """Hall counts of one family, for k, m = 1 … N+1 (N+1: from the hole start / to its end)."""
    N = len(lo)
    nH = {H: lo.count(H) for H in 'XY'}
    out = []
    for k in range(1, N + 2):
        for m in range(1, N + 2):
            tot = 0
            for H in 'XY':
                n = nH[H]
                kH = lo[N - k:].count(H) if k <= N else n + 1
                mH = lc[:m].count(H) if m <= N else n + 1
                s = min(kH, n) if fam[0] == 'o' else min(max(kH - 1, 0), n)
                e = min(mH, n) if fam[1] == 'o' else min(max(mH - 1, 0), n)
                tot += min(s, e)
            out.append(tot)
    return out


def interval_gaps(N):
    """For every (k, m) the gap index range it covers."""
    G = gaps(N)
    res = []
    for k in range(1, N + 2):
        for m in range(1, N + 2):
            a = G.index(f'L{N - k + 1}') if k <= N else 0
            if m == N + 1:
                b = len(G) - 1
            elif m == 1:
                b = G.index(f'L{N}')
            else:
                b = G.index(f'R{m}')
            res.append((a, b))
    return res


def main(N, fams, restarts, steps, seed, W=2):
    """Minimise the number of valid pairings of width <= W (the source has width > W)."""
    rng = random.Random(seed)
    skel = 'b' * N + 'ss' + 'a' * N
    P = []
    for nx in range(N + 1):
        perms = sorted(set(itertools.permutations('X' * nx + 'Y' * (N - nx))))
        P += [(''.join(lo), ''.join(lc)) for lo in perms for lc in perms]
    thin = np.array([min_width(skel, skeleton_lv(N, lo, lc), wmax=W) is not None for lo, lc in P])
    C = {f: np.array([fam_counts(lo, lc, f) for lo, lc in P], dtype=np.int16) for f in fams}
    IG = interval_gaps(N)
    ng = len(gaps(N))
    # gap -> indicator matrix of intervals containing it
    M = np.zeros((ng, len(IG)), dtype=np.int16)
    for j, (a, b) in enumerate(IG):
        M[a:b + 1, j] = 1
    thick = [i for i in range(len(P)) if not thin[i]]
    print(f'N={N}: {len(P)} pairings, {len(thick)} of width > {W}; families {fams}', flush=True)

    def n_thin_valid(place):
        ok = np.ones(len(P), dtype=bool)
        for f in fams:
            cnt = np.zeros(ng, dtype=np.int16)
            for g in place[f]:
                cnt[g] += 1
            U = cnt @ M
            ok &= np.all(C[f] <= U, axis=1)
        return int((ok & thin).sum()), int(ok.sum())

    best = None
    for r in range(restarts):
        src = rng.choice(thick)
        lv = pairing_levels(*P[src])
        wins = {f: [window(N, lv, H, l, f) for H in 'XY' for l in range(len(lv[H]))] for f in fams}
        place = {f: [rng.randint(a, b) for (a, b) in wins[f]] for f in fams}
        cur = n_thin_valid(place)
        for _ in range(steps):
            f = rng.choice(fams)
            j = rng.randrange(len(place[f]))
            old = place[f][j]
            a, b = wins[f][j]
            place[f][j] = rng.randint(a, b)
            new = n_thin_valid(place)
            if new[0] <= cur[0]:
                cur = new
            else:
                place[f][j] = old
            if cur[0] == 0:
                break
        if best is None or cur[0] < best[0]:
            best = (cur[0], cur[1], P[src], {f: list(place[f]) for f in fams})
            print(f'  restart {r}: thin valid {cur[0]}, all valid {cur[1]}, source {P[src]}, '
                  f'placement {best[3]}', flush=True)
        if best[0] == 0:
            break
    print('best', best[:2])


if __name__ == "__main__":
    main(int(sys.argv[1]), sys.argv[2].split(','), int(sys.argv[3]), int(sys.argv[4]),
         int(sys.argv[5]), int(sys.argv[6]) if len(sys.argv) > 6 else 2)
