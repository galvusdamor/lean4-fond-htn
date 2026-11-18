"""Rolling cuts: how many segments must be open at the same time?  (HD2_LU.md §6.10)

The K-cut search of §6.7 fixes K cut points in advance.  A *rolling* search places a cut only when
it needs one, inside the unprocessed part of an open segment, and drops a segment once its two
frontiers have met.  For a fixed W ("width": at most W segments open at once) it is still a VASS:
the classes of the open segments are renumbered when a segment is split or dropped.

Abstract model as in `forcing.py` (cont = b < u < a, stop = s).  For a fixed plan and
interpretation, the processed positions only grow; an end of an unprocessed interval can be
processed as soon as its level exists (this never hurts), a position inside an interval only by a
new cut, which splits the interval.  `min_width` is the least W for which every position can be
processed with at most W unprocessed intervals at any time.  With `free_u` the u's never block
(a lower bound, as in `forcing.py`).
"""
import sys

from forcing import interpretations, hall_ok


def owners(seq, lv, free_u):
    """Owner (hole, depth) of every b, a, s; levels are created in depth order."""
    owner = {}
    for H in 'XY':
        pairs, s = lv[H]
        for j, (b, a) in enumerate(pairs):
            owner[b] = (H, j)
            owner[a] = (H, j)
        owner[s] = (H, len(pairs))
    if not free_u:
        raise NotImplementedError
    return owner


def gaps(done):
    out, i, n = [], 0, len(done)
    while i < n:
        if done[i]:
            i += 1
            continue
        j = i
        while j + 1 < n and not done[j + 1]:
            j += 1
        out.append((i, j))
        i = j + 1
    return out


def min_width(seq, lv, wmax=6):
    owner = owners(seq, lv, True)
    n = len(seq)

    def created(done):
        c = {}
        for H in 'XY':
            pairs, s = lv[H]
            j = 0
            while j < len(pairs) and done[pairs[j][0]] and done[pairs[j][1]]:
                j += 1
            c[H] = j
        return c

    def ok(p, c):
        if p not in owner:
            return True
        H, j = owner[p]
        return j <= c[H]

    def close(done):
        done = list(done)
        changed = True
        while changed:
            changed = False
            c = created(done)
            for (i, j) in gaps(done):
                for p in (i, j):
                    if not done[p] and ok(p, c):
                        done[p] = True
                        changed = True
        return tuple(done)

    for W in range(1, wmax + 1):
        start = close((False,) * n)
        seen = {start}
        stack = [start]
        found = False
        while stack:
            d = stack.pop()
            if all(d):
                found = True
                break
            gs = gaps(d)
            if len(gs) >= W:
                continue
            c = created(d)
            for (i, j) in gs:
                for p in range(i + 1, j):
                    if ok(p, c):
                        nd = list(d)
                        nd[p] = True
                        nd = close(nd)
                        if len(gaps(nd)) <= W and nd not in seen:
                            seen.add(nd)
                            stack.append(nd)
        if found:
            return W
    return None


def width_lb(seq, wmax=6):
    """Least width over the valid interpretations (u's free): a lower bound for the plan."""
    best = None
    valid = 0
    for lv in interpretations(seq):
        if not hall_ok(seq, lv):
            continue
        valid += 1
        w = min_width(seq, lv, wmax if best is None else best - 1)
        if w is not None and (best is None or w < best):
            best = w
            if best == 1:
                break
    return best, valid


if __name__ == "__main__":
    for s in sys.argv[1:]:
        print(s, width_lb(s))
