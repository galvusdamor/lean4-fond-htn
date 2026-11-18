"""Is an L-shaped interpretation always available?  (HD2_LU.md §6.11)

An interpretation is an *L* if one hole opens all its levels first and also closes them first:
the lockstep part then has a single 2143-crossing, which one cut resolves.

    python3 lshape.py avail CONT N SEED [sep]   # random plans: does some valid interpretation
                                                # have an L (lockstep box) shape?
    python3 lshape.py dominate NMAX             # one floating type anchored on both sides,
                                                # bottoms adjacent: is every pairing's Hall
                                                # count dominated by some L pairing?
"""
import itertools
import random
import sys

from rich import CONTS, interpretations, valid, random_word


def is_L(lv):
    """Adjacent bottoms: one hole takes the first openings and the first closings."""
    ops = sorted(b for H in 'XY' for b, a in lv[H][0])
    cls = sorted(a for H in 'XY' for b, a in lv[H][0])
    for F in 'XY':
        nf = len(lv[F][0])
        if {b for b, a in lv[F][0]} == set(ops[:nf]) and {a for b, a in lv[F][0]} == set(cls[:nf]):
            return True
    return False


def box_is_L(lv):
    """Separated bottoms: the lockstep box (F's levels closing after G's bottom, and all of G)
    is an L, or one of its two parts is empty."""
    F, G = sorted('XY', key=lambda H: lv[H][1])
    fbox = [(b, a) for (b, a) in lv[F][0] if a > lv[G][1]]
    gl = lv[G][0]
    if not fbox or not gl:
        return True
    for P, Q in ((fbox, gl), (gl, fbox)):
        if max(b for b, a in P) < min(b for b, a in Q) and max(a for b, a in P) < min(a for b, a in Q):
            return True
    return False


def avail(name, count, seed, separated=False):
    c = CONTS[name]
    rng = random.Random(seed)
    test = box_is_L if separated else is_L
    yes = no = 0
    for _ in range(count):
        w = None
        while w is None:
            w = random_word(rng, c, 3, 3, pins=rng.random() < 0.5, adjacent=not separated)
        for _ in range(rng.randint(0, 3)):          # perturb: move a floating task
            l = list(w)
            i = rng.choice([i for i, e in enumerate(l) if e in c.types])
            x = l.pop(i)
            l.insert(rng.randrange(len(l) + 1), x)
            w = ''.join(l)
        vals = [lv for lv in interpretations(w) if valid(w, c, lv)]
        if not vals:
            continue
        if any(test(lv) for lv in vals):
            yes += 1
        else:
            no += 1
            print('  no L:', w, len(vals), 'valid interpretations', flush=True)
    print(name, 'separated' if separated else 'adjacent', 'L available', yes, 'not', no)


def hall_counts(lo, lc):
    """count(k, m): levels whose opening is among the last k and closing among the first m."""
    N = len(lo)
    return {(k, m): min(lo[N - k:].count('X'), lc[:m].count('X'))
            + min(k - lo[N - k:].count('X'), m - lc[:m].count('X'))
            for k in range(N + 1) for m in range(N + 1)}


def dominate(nmax):
    bad = total = 0
    for N in range(2, nmax + 1):
        Ls = [hall_counts('X' * n + 'Y' * (N - n), 'X' * n + 'Y' * (N - n)) for n in range(N + 1)]
        for nx in range(1, N):
            perms = set(itertools.permutations('X' * nx + 'Y' * (N - nx)))
            for lo in perms:
                for lc in perms:
                    c = hall_counts(lo, lc)
                    total += 1
                    if not any(all(L[q] <= c[q] for q in c) for L in Ls):
                        bad += 1
                        print('  not dominated:', ''.join(lo), ''.join(lc))
    print('pairings', total, 'not dominated by any L', bad)


if __name__ == "__main__":
    if sys.argv[1] == 'avail':
        avail(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), 'sep' in sys.argv[5:])
    else:
        dominate(int(sys.argv[2]))
