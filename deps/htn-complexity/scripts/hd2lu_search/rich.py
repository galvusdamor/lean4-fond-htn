"""Can richer methods force thick crossings?  (HD2_LU.md §6.11)

Abstract model with several floating task types.  A plan is a word over

* `b`, `a`, `s` — opening (B-block), closing (A-block), bottom (stop) of a level;
* `<` — a task `t` of the initial network with `t ≺ c₂`: hole Y starts after it;
* `>` — a task `t` with `c₁ ≺ t`: hole X ends before it;
* any other letter — a floating task (U-task) of that type.

`Cont(types, prec)`: `types[τ] = (after_b, before_a)` says whether `τ` is ordered after the
level's own `b` and before its own `a`; `prec` holds pairs `(τ, τ')` with `τ ≺ τ'` inside a level.
A floating task of type `τ` of level `j` lies after the level's own `b` (if `after_b`), else after
the parent's `b`, and before its own `a` (if `before_a`), else before the parent's `a`.

`valid(word, cont, lv)` decides an interpretation exactly (backtracking over the floating tasks in
time order); `width_lb(word, cont)` is the least width (`width.min_width`, floating tasks free) over
all valid interpretations.
"""
import random
import sys

from width import min_width


class Cont:
    def __init__(self, types, prec=()):
        self.types = dict(types)
        self.prec = frozenset(prec)
        self.preds = {t: frozenset(p for (p, q) in self.prec if q == t) for t in self.types}


def interpretations(word):
    """Assign every b, a, s to hole X or Y (both stack-like), respecting the pins."""
    lt = word.index('<') if '<' in word else -1
    gt = word.index('>') if '>' in word else len(word)
    ev = [(i, e) for i, e in enumerate(word) if e in 'bas']
    out = []

    def rec(k, st, lv):
        if k == len(ev):
            if all(st[H][0] == 'asc' and not st[H][1] for H in 'XY'):
                out.append({H: (sorted(lv[H][0]), lv[H][1]) for H in 'XY'})
            return
        i, e = ev[k]
        for H in 'XY':
            if (H == 'Y' and i < lt) or (H == 'X' and i > gt):
                continue
            phase, stack = st[H]
            if e == 'b' and phase == 'desc':
                rec(k + 1, {**st, H: (phase, stack + (i,))}, lv)
            elif e == 's' and phase == 'desc':
                rec(k + 1, {**st, H: ('asc', stack)}, {**lv, H: (lv[H][0], i)})
            elif e == 'a' and phase == 'asc' and stack:
                rec(k + 1, {**st, H: (phase, stack[:-1])},
                    {**lv, H: (lv[H][0] + ((stack[-1], i),), lv[H][1])})

    rec(0, {'X': ('desc', ()), 'Y': ('desc', ())}, {'X': ((), None), 'Y': ((), None)})
    return out


def windows(word, cont, lv):
    lt = word.index('<') if '<' in word else -1
    gt = word.index('>') if '>' in word else len(word)
    slots = []
    for H in 'XY':
        pairs, _ = lv[H]
        lo0, hi0 = (lt, len(word)) if H == 'Y' else (-1, gt)
        for j, (b, a) in enumerate(pairs):
            pb, pa = (pairs[j - 1] if j else (lo0, hi0))
            for t, (ab, ba) in cont.types.items():
                slots.append(((H, j), t, b if ab else pb, a if ba else pa))
    return slots


def edf(word, typ, slots):
    """One type, no order constraints: earliest-deadline-first is exact for interval windows."""
    open_, wins = [], sorted((lo, hi) for (_, t, lo, hi) in slots if t == typ)
    k = 0
    for i, e in enumerate(word):
        while k < len(wins) and wins[k][0] < i:
            open_.append(wins[k][1])
            k += 1
        if any(hi <= i for hi in open_):
            return False
        if e == typ:
            if not open_:
                return False
            open_.remove(min(open_))
    return k == len(wins) and not open_


def valid(word, cont, lv):
    slots = windows(word, cont, lv)
    ex = [(i, e) for i, e in enumerate(word) if e in cont.types]
    if len(ex) != len(slots):
        return False
    if not cont.prec:
        return all(edf(word, t, slots) for t in cont.types)
    slots = [((lvl, t), t, lo, hi) for (lvl, t, lo, hi) in slots]
    preds = {key: frozenset((key[0], p) for p in cont.preds[t]) for (key, t, lo, hi) in slots}
    memo = {}

    def rec(k, filled):
        # filled: frozenset of slot keys; executions are taken in time order, so a filled
        # predecessor is always earlier
        if k == len(ex):
            return True
        if (k, filled) in memo:
            return memo[(k, filled)]
        t_now, typ = ex[k]
        ok = False
        if all(key in filled or hi > t_now for (key, t, lo, hi) in slots):
            tried = set()
            for (key, t, lo, hi) in slots:
                if t != typ or key in filled or not (lo < t_now < hi) or not preds[key] <= filled:
                    continue
                sig = (lo, hi, frozenset(p for p in cont.types if (key[0], p) in filled))
                if sig in tried:
                    continue
                tried.add(sig)
                if rec(k + 1, filled | {key}):
                    ok = True
                    break
        memo[(k, filled)] = ok
        return ok

    return rec(0, frozenset())


def width_lb(word, cont, wmax=6):
    best, nvalid = None, 0
    for lv in interpretations(word):
        if not valid(word, cont, lv):
            continue
        nvalid += 1
        w = min_width(word, lv, wmax if best is None else best - 1)
        if w is not None and (best is None or w < best):
            best = w
            if best == 1:
                break
    return best, nvalid


def shuffle2(rng, X, Y):
    X, Y, out = list(X), list(Y), []
    while X or Y:
        if not Y or (X and rng.random() < 0.5):
            out.append(X.pop(0))
        else:
            out.append(Y.pop(0))
    return out


def box(lv):
    """The part of an interpretation handled in lockstep by the one-stack search (§6.10): the
    levels of the hole F that bottoms first and close after G's bottom, and all of G.  F's other
    levels are left to the stack and do not count."""
    F, G = sorted('XY', key=lambda H: lv[H][1])
    sG = lv[G][1]
    out = {G: lv[G]}
    out[F] = ([(b, a) for (b, a) in lv[F][0] if a > sG], lv[F][1])
    return out


def box_width_lb(word, cont, wmax=6):
    """Least width of the lockstep box over all valid interpretations."""
    best, nvalid = None, 0
    for lv in interpretations(word):
        if not valid(word, cont, lv):
            continue
        nvalid += 1
        w = min_width(word, box(lv), wmax if best is None else best - 1)
        if w is not None and (best is None or w < best):
            best = w
            if best == 1:
                break
    return best, nvalid


def random_word(rng, cont, nx, ny, pins=True, adjacent=False):
    """A plan with a random interleaving of two chains and floating tasks inside their windows.
    With `adjacent` the two bottoms are next to each other (no phase 2)."""
    if adjacent:
        ev = (shuffle2(rng, ['bX'] * nx, ['bY'] * ny) + ['sX', 'sY']
              + shuffle2(rng, ['aX'] * nx, ['aY'] * ny))
    else:
        ev = shuffle2(rng, ['bX'] * nx + ['sX'] + ['aX'] * nx, ['bY'] * ny + ['sY'] + ['aY'] * ny)
    if pins:
        fy = next(i for i, e in enumerate(ev) if e[1] == 'Y')
        ev.insert(rng.randint(0, fy), '<')
        lx = max(i for i, e in enumerate(ev) if len(e) == 2 and e[1] == 'X')
        ev.insert(rng.randint(lx + 1, len(ev)), '>')
    word = ''.join(e[0] for e in ev)
    lv = {}
    for H in 'XY':
        st, pairs, s = [], [], None
        for i, e in enumerate(ev):
            if len(e) == 2 and e[1] == H:
                if e[0] == 'b':
                    st.append(i)
                elif e[0] == 's':
                    s = i
                else:
                    pairs.append((st.pop(), i))
        lv[H] = (sorted(pairs), s)
    ins = windows(word, cont, lv)
    # place each floating task inside its window, respecting the in-level order
    placed = {}
    order = sorted(cont.types, key=lambda t: len(cont.preds[t]))
    pos = []
    for (lvl, t, lo, hi) in sorted(ins, key=lambda x: order.index(x[1])):
        lo2 = max([lo] + [placed[(lvl, p)] for p in cont.preds[t]])
        if lo2 + 1 > hi:
            return None
        p = rng.uniform(lo2 + 0.01, hi - 0.01)
        placed[(lvl, t)] = p
        pos.append((p, t))
    out = list(word)
    for p, t in sorted(pos, reverse=True):
        out.insert(int(p) + 1, t)
    return ''.join(out)


def climb(cont, nx, ny, restarts, steps, seed, pins=True, adjacent=False, score=None):
    """Hill climbing on the positions of floating tasks and pins, maximising the width bound
    (`score`, default `width_lb`)."""
    width_lb_ = score or width_lb
    rng = random.Random(seed)
    best = None
    for r in range(restarts):
        w = None
        while w is None:
            w = random_word(rng, cont, nx, ny, pins, adjacent)
        cur = width_lb_(w, cont)
        if cur[0] is None:
            continue
        for _ in range(steps):
            i = rng.randrange(len(w))
            if w[i] not in cont.types and w[i] not in '<>':
                continue
            j = rng.randrange(len(w))
            l = list(w)
            c = l.pop(i)
            l.insert(j, c)
            w2 = ''.join(l)
            sc = width_lb_(w2, cont)
            if sc[0] is not None and (sc[0], -sc[1]) >= (cur[0], -cur[1]):
                w, cur = w2, sc
        if best is None or (cur[0], -cur[1]) > (best[0][0], -best[0][1]):
            best = (cur, w)
            print(r, best, flush=True)
    return best


CONTS = {
    'u|ba': Cont({'u': (True, True)}),
    'u|b,v|a': Cont({'u': (True, False), 'v': (False, True)}),
    'u|b<v|a': Cont({'u': (True, False), 'v': (False, True)}, {('u', 'v')}),
    'v|a<u|b': Cont({'u': (True, False), 'v': (False, True)}, {('v', 'u')}),
    'u<v|ba': Cont({'u': (True, True), 'v': (True, True)}, {('u', 'v')}),
    'u,v free': Cont({'u': (False, False), 'v': (False, False)}, {('u', 'v')}),
    'u0,v|b<w|a': Cont({'u': (False, False), 'v': (True, False), 'w': (False, True)},
                       {('u', 'w'), ('v', 'w')}),
    'u|b<v0<w|a': Cont({'u': (True, False), 'v': (False, False), 'w': (False, True)},
                       {('u', 'v'), ('v', 'w'), ('u', 'w')}),
}

if __name__ == "__main__":
    name, nx, ny, restarts, steps, seed = sys.argv[1], *map(int, sys.argv[2:7])
    climb(CONTS[name], nx, ny, restarts, steps, seed, adjacent='adjacent' in sys.argv[7:],
          score=box_width_lb if 'box' in sys.argv[7:] else None)
