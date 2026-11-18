"""Forcing thick bubbles with unordered floating types, exactly.  (HD2_LU.md §6.11)

Bottoms adjacent; N openings, then the bottoms, then N closings.  A floating type is anchored by
its *family*: its window starts after the level's own `b` (`o`) or the parent's (`p`), and ends
before its own `a` (`o`) or the parent's (`p`); level 1's parent is the hole boundary.  For one
unordered type with interval windows, earliest-deadline-first decides validity exactly.

Floating tasks live in gaps: `G0` before the first opening, `L1 … LN` after each opening (`LN`
includes the middle), `R2 … RN` before each later closing, `E` after the last closing.

`search(N, fams, tries)` takes a thick pairing (width ≥ 3), places one task of each type per level
inside its window, and computes the least width over *all* pairings valid for every type.  A
result ≥ 3 is a plan (abstract) on which every valid interpretation has a thick bubble.

    python3 famsearch.py N FAMS TRIES SEED     # e.g.  python3 famsearch.py 8 op,po 300 1
"""
import itertools
import random
import sys

from width import min_width


def gaps(N):
    return ['G0'] + [f'L{i}' for i in range(1, N + 1)] + [f'R{j}' for j in range(2, N + 1)] + ['E']


def pairing_levels(lo, lc):
    """Levels of each hole as (opening index, closing index), 1-based, outermost first."""
    N = len(lo)
    lv = {}
    for H in 'XY':
        ops = [i + 1 for i in range(N) if lo[i] == H]
        cls = [j + 1 for j in range(N) if lc[j] == H]
        lv[H] = list(zip(ops, reversed(cls)))
    return lv


def window(N, lv, H, l, fam):
    """Gap index range [lo, hi] of the window of level l (0-based) of hole H for family fam."""
    G = gaps(N)
    o, c = lv[H][l]
    if fam[0] == 'o':
        start = G.index(f'L{o}')
    else:
        start = G.index(f'L{lv[H][l - 1][0]}') if l else 0
    def before(cl):
        return G.index(f'R{cl}') if cl >= 2 else G.index(f'L{N}')
    if fam[1] == 'o':
        end = before(c)
    else:
        end = before(lv[H][l - 1][1]) if l else len(G) - 1
    return start, end


def edf_ok(wins, counts):
    """One task per window; counts[g] tasks in gap g.  Exact for intervals."""
    wins = sorted(wins)
    open_, k = [], 0
    for g, cnt in enumerate(counts):
        while k < len(wins) and wins[k][0] <= g:
            open_.append(wins[k][1])
            k += 1
        if any(hi < g for hi in open_):
            return False
        for _ in range(cnt):
            if not open_:
                return False
            open_.remove(min(open_))
    return k == len(wins) and not open_


def skeleton_lv(N, lo, lc):
    lv = pairing_levels(lo, lc)
    pos = lambda o: o - 1                       # openings at 0..N-1, bottoms N, N+1
    cpos = lambda c: N + 1 + c                  # closings at N+2 .. 2N+1
    return {H: (sorted((pos(o), cpos(c)) for o, c in lv[H]), N if H == 'X' else N + 1) for H in 'XY'}


def search(N, fams, tries, seed):
    rng = random.Random(seed)
    skel = 'b' * N + 'ss' + 'a' * N
    pairs = []
    for nx in range(N + 1):
        perms = sorted(set(itertools.permutations('X' * nx + 'Y' * (N - nx))))
        pairs += [(lo, lc) for lo in perms for lc in perms]
    width = {}

    def w(i):
        if i not in width:
            lo, lc = pairs[i]
            width[i] = min_width(skel, skeleton_lv(N, lo, lc), wmax=8)
        return width[i]

    thick = [i for i in range(len(pairs)) if w(i) >= 3]
    print(f'N={N} pairings {len(pairs)}, thick {len(thick)}, families {fams}', flush=True)
    wins_of = {}

    def wins(i, fam):
        if (i, fam) not in wins_of:
            lv = pairing_levels(*pairs[i])
            wins_of[(i, fam)] = [window(N, lv, H, l, fam) for H in 'XY' for l in range(len(lv[H]))]
        return wins_of[(i, fam)]

    best = 0
    for t in range(tries):
        src = rng.choice(thick)
        counts = []
        for fam in fams:
            cnt = [0] * len(gaps(N))
            for (a, b) in wins(src, fam):
                r = rng.random()
                g = a if r < 0.4 else b if r < 0.8 else rng.randint(a, b)
                cnt[g] += 1
            counts.append(cnt)
        valid = [i for i in range(len(pairs))
                 if all(edf_ok(wins(i, f), cnt) for f, cnt in zip(fams, counts))]
        least = min(w(i) for i in valid)
        if least > best:
            best = least
            print(f'  try {t}: least width {least} over {len(valid)} valid pairings; source',
                  ''.join(pairs[src][0]), ''.join(pairs[src][1]), counts, flush=True)
    print('best', best)


if __name__ == "__main__":
    search(int(sys.argv[1]), sys.argv[2].split(','), int(sys.argv[3]), int(sys.argv[4]))
