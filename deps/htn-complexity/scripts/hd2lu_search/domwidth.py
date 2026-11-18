"""Which widths can unordered floating tasks force at all?  (HD2_LU.md §6.13)

For unordered floating types, validity of an interpretation depends only on its Hall counts (one
count function per anchoring family, `forcethick.fam_counts`), and smaller counts are easier.
So if a pairing Q has counts ≤ those of P in every family, no placement of unordered tasks can
make P valid and Q invalid.  `check(N, W, fams)` lists the pairings of width > W that are *not*
dominated by any pairing of width ≤ W.  If there are none, unordered tasks of these families
can never force width > W on N levels.

    python3 domwidth.py N W [FAMS]
"""
import itertools
import sys

import numpy as np

from famsearch import skeleton_lv
from width import min_width


def all_pairings(N):
    out = []
    for nx in range(N + 1):
        perms = sorted(set(itertools.permutations('X' * nx + 'Y' * (N - nx))))
        out += [(''.join(lo), ''.join(lc)) for lo in perms for lc in perms]
    return out


def counts(P, N, fam, chunk=50000):
    """Hall counts for all pairings at once, k, m = 1 … N+1; shape (len(P), (N+1)²)."""
    if len(P) > chunk:
        return np.concatenate([counts(P[i:i + chunk], N, fam) for i in range(0, len(P), chunk)])
    lo = np.array([[c == 'X' for c in p[0]] for p in P], dtype=np.int16)
    lc = np.array([[c == 'X' for c in p[1]] for p in P], dtype=np.int16)
    nX = lo.sum(axis=1)
    n = {'X': nX, 'Y': N - nX}
    # k-th entry: number among the last k openings (k = 1..N), and the hole-start value
    kX = np.cumsum(lo[:, ::-1], axis=1)                     # (P, N): last 1..N
    mX = np.cumsum(lc, axis=1)                               # (P, N): first 1..N
    K = {'X': kX, 'Y': np.arange(1, N + 1)[None, :] - kX}
    M = {'X': mX, 'Y': np.arange(1, N + 1)[None, :] - mX}
    tot = 0
    for H in 'XY':
        nh = n[H][:, None]
        kH = np.concatenate([K[H], nh + 1], axis=1)          # k = N+1: from the hole start
        mH = np.concatenate([M[H], nh + 1], axis=1)          # m = N+1: to the hole end
        s = np.minimum(kH, nh) if fam[0] == 'o' else np.minimum(np.maximum(kH - 1, 0), nh)
        e = np.minimum(mH, nh) if fam[1] == 'o' else np.minimum(np.maximum(mH - 1, 0), nh)
        tot = tot + np.minimum(s[:, :, None], e[:, None, :])
    return tot.reshape(len(P), -1).astype(np.int16)


def check(N, W, fams):
    P = all_pairings(N)
    skel = 'b' * N + 'ss' + 'a' * N
    thin = np.array([min_width(skel, skeleton_lv(N, lo, lc), wmax=W) is not None for lo, lc in P])
    C = np.concatenate([counts(P, N, f) for f in fams], axis=1)
    T = C[thin]
    bad = []
    for i in np.where(~thin)[0]:
        dom = False
        for j in range(0, len(T), 100000):
            if np.any(np.all(T[j:j + 100000] <= C[i], axis=1)):
                dom = True
                break
        if not dom:
            bad.append(P[i])
    print(f'N={N}, W={W}, families {fams}: {len(P)} pairings, {int((~thin).sum())} of width > {W}, '
          f'{len(bad)} not dominated by width <= {W}', flush=True)
    for b in bad[:6]:
        print('   ', b)
    return bad


if __name__ == "__main__":
    fams = sys.argv[3].split(',') if len(sys.argv) > 3 else ['oo', 'op', 'po', 'pp']
    check(int(sys.argv[1]), int(sys.argv[2]), fams)
