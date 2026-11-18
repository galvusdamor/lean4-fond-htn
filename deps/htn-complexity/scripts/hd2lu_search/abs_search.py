"""Empirical test of the counting abstraction for 2-HD ∩ L (HD2_LU.md §6.4.1).

Core shape: t0 = {c1, c2} ∪ primitive chain (unordered with c1, c2);
cont = (P ∪ {h}, <), P = B ∪ U ∪ A relative to h; stop = S.

exact_depths(inst, N):   {(n1, n2) : N(n1, n2) has an executable linearisation}, n1, n2 ≤ N
abstract_depths(inst, N): the same set according to the abstract early-decomposition
                          bidirectional search with *counted* locked U-pieces.
"""
import itertools
import random
from collections import Counter
from functools import lru_cache
import sys

sys.setrecursionlimit(100000)


def closure(pairs):
    rel = set(pairs)
    while True:
        new = {(x, z) for (x, y) in rel for (y2, z) in rel if y == y2} - rel
        if not new:
            return frozenset(rel)
        rel |= new


class Inst:
    def __init__(self, facts, acts, kind, order, S, Sorder, T, Torder, lab, init, goal):
        self.facts, self.acts = facts, acts          # acts: name -> (pre, add, del)
        self.kind = kind                              # P-task -> 'B' | 'U' | 'A'
        self.P = frozenset(kind)
        self.Bs = frozenset(x for x in kind if kind[x] == 'B')
        self.Us = frozenset(x for x in kind if kind[x] == 'U')
        self.As = frozenset(x for x in kind if kind[x] == 'A')
        # in-level order on P ∪ {h}
        o = set(order) | {(b, 'h') for b in self.Bs} | {('h', a) for a in self.As}
        self.order = closure(o)
        self.S, self.Sorder = frozenset(S), closure(Sorder)
        self.T, self.Torder = frozenset(T), closure(Torder)
        self.lab = lab                                # task id -> action
        self.init, self.goal = frozenset(init), frozenset(goal)
        self.states = [frozenset(c) for r in range(len(facts) + 1)
                       for c in itertools.combinations(facts, r)]

    def app(self, s, a):
        return self.acts[a][0] <= s

    def nxt(self, s, a):
        pre, add, dele = self.acts[a]
        return frozenset((s - dele) | add)

    def pre_states(self, sb, a):
        return [s for s in self.states if self.app(s, a) and self.nxt(s, a) == sb]


# ------------------------------------------------------------------ exact solver
def exact_solvable(I, n1, n2):
    tasks, lab, preds = [], {}, {}
    ordp = set()
    for t in I.T:
        tasks.append(('T', 0, t)); lab[('T', 0, t)] = I.lab[t]
    ordp |= {(('T', 0, x), ('T', 0, y)) for (x, y) in I.Torder}
    for H, n in (('X', n1), ('Y', n2)):
        if n < 0:
            continue
        levels = {}
        for l in range(1, n + 1):
            levels[l] = [(H, l, x) for x in I.P]
            for x in I.P:
                lab[(H, l, x)] = I.lab[x]
            ordp |= {((H, l, x), (H, l, y)) for (x, y) in I.order if 'h' not in (x, y)}
        levels[n + 1] = [(H, n + 1, s) for s in I.S]
        for s in I.S:
            lab[(H, n + 1, s)] = I.lab[s]
        ordp |= {((H, n + 1, x), (H, n + 1, y)) for (x, y) in I.Sorder}
        for l in range(1, n + 1):
            deeper = [t for j in range(l + 1, n + 2) for t in levels[j]]
            for b in I.Bs:
                ordp |= {((H, l, b), t) for t in deeper}
            for a in I.As:
                ordp |= {(t, (H, l, a)) for t in deeper}
        tasks += [t for l in levels for t in levels[l]]
    idx = {t: i for i, t in enumerate(tasks)}
    pm = [0] * len(tasks)
    for (x, y) in ordp:
        pm[idx[y]] |= 1 << idx[x]
    full = (1 << len(tasks)) - 1
    labs = [lab[t] for t in tasks]

    @lru_cache(maxsize=None)
    def go(done, s):
        if done == full:
            return I.goal <= s
        for i in range(len(tasks)):
            if not (done >> i) & 1 and (pm[i] & done) == pm[i] and I.app(s, labs[i]):
                if go(done | (1 << i), I.nxt(s, labs[i])):
                    return True
        return False

    r = go(0, I.init)
    go.cache_clear()
    return r


def exact_depths(I, N):
    return {(a, b) for a in range(N + 1) for b in range(N + 1) if exact_solvable(I, a, b)}


# ------------------------------------------------------------------ abstract search
# hole = (st, mode, free, sh, locked, cur, dp, depth)
#   st: 'init' | 'open' | 'closed';  mode: None | 'A' | 'B'
#   free, locked: sorted tuples of (Ustate, count);  sh, dp: frozenset or None
#   cur: frozenset ⊆ P ∪ {h} (open) or ⊆ S (closed: the bottom)

def ms_add(ms, x, k=1):
    c = Counter(dict(ms)); c[x] += k
    return tuple(sorted(((s, n) for s, n in c.items() if n > 0), key=lambda p: sorted(p[0])))


def ms_sub(ms, x):
    c = Counter(dict(ms)); c[x] -= 1
    assert c[x] >= 0
    return tuple(sorted(((s, n) for s, n in c.items() if n > 0), key=lambda p: sorted(p[0])))


class Abs:
    def __init__(self, I, N):
        self.I, self.N = I, N

    def minimal(self, x, rem):
        return all((y, x) not in self.I.order for y in rem)

    def maximal(self, x, rem):
        return all((x, y) not in self.I.order for y in rem)

    def pend(self, m):
        return self.I.As if m == 'A' else self.I.Bs

    def norm(self, h):
        """Normalise a hole; returns a list (branching on choices from `locked`)."""
        I = self.I
        st, mode, free, sh, locked, cur, dp, depth = h
        free = tuple((s, n) for s, n in free if s)
        if mode is None:
            return [(st, mode, free, sh, locked, cur, dp, depth)]
        P = self.pend(mode)
        # shallow end finished its pending part: release the next locked piece
        if sh is not None and not (sh & P):
            if sh & I.Us:
                free = ms_add(free, sh & I.Us)
            sh = None
            if locked:
                outs = []
                for (sig, n) in locked:
                    nl = ms_sub(locked, sig)
                    outs += self.norm((st, mode, free, P | sig, nl, cur, dp, depth))
                return outs
        # the deep end is also the shallowest pending level and its pending part is done
        if sh is None and not locked and dp is not None and not (dp & P):
            if dp & I.Us:
                free = ms_add(free, dp & I.Us)
            dp = None
        # closed hole: deep end complete and bottom done -> move up
        if st == 'closed' and dp is not None and not cur and not dp:
            if locked:
                outs = []
                for (sig, n) in locked:
                    nl = ms_sub(locked, sig)
                    outs += self.norm((st, mode, free, sh, nl, cur, P | sig, depth))
                return outs
            elif sh is not None:
                dp, sh = sh, None
                return self.norm((st, mode, free, sh, locked, cur, dp, depth))
            else:
                dp = None
        pending = sh is not None or bool(locked) or dp is not None
        if not pending:
            mode = None
        return [(st, mode, tuple((s, n) for s, n in free if s), sh, locked, cur, dp, depth)]

    def flags(self, h):
        """(Bup, Aup) for the levels sh, locked, dp, cur/bottom."""
        st, mode, free, sh, locked, cur, dp, depth = h
        dp_shallow = sh is None and not locked
        if mode is None:
            T = (True, True)
            return {'sh': T, 'locked': T, 'dp': T, 'cur': T}
        if mode == 'A':
            return {'sh': (True, True), 'locked': (True, False),
                    'dp': (True, dp_shallow), 'cur': (True, False)}
        return {'sh': (True, True), 'locked': (False, True),
                'dp': (dp_shallow, True), 'cur': (False, True)}

    def hole_moves(self, h, sf, sb):
        """Yield (direction, action, new_hole) for steps inside one hole; direction 'f' or 'b'."""
        I = self.I
        st, mode, free, sh, locked, cur, dp, depth = h
        if st == 'init':
            yield ('d', None, ('open', None, (), None, (), I.P | {'h'}, None, 1)) if self.N >= 1 else None
            yield ('d', None, ('closed', None, (), None, (), I.S, None, 0))
            return
        fl = self.flags(h)

        def upd(**kw):
            d = dict(st=st, mode=mode, free=free, sh=sh, locked=locked, cur=cur, dp=dp, depth=depth)
            d.update(kw)
            return (d['st'], d['mode'], d['free'], d['sh'], d['locked'], d['cur'], d['dp'], d['depth'])

        # free pieces (both A and B of the level and above done)
        for (sig, n) in free:
            for u in sig:
                if self.minimal(u, sig):
                    yield ('f', u, upd(free=ms_add(ms_sub(free, sig), sig - {u})))
                if self.maximal(u, sig):
                    yield ('b', u, upd(free=ms_add(ms_sub(free, sig), sig - {u})))
        # locked pieces: one direction only
        for (sig, n) in locked:
            for u in sig:
                Bup, Aup = fl['locked']
                if Bup and self.minimal(u, sig | (I.Bs if mode == 'B' else frozenset())):
                    yield ('f', u, upd(locked=ms_add(ms_sub(locked, sig), sig - {u})))
                if Aup and self.maximal(u, sig | (I.As if mode == 'A' else frozenset())):
                    yield ('b', u, upd(locked=ms_add(ms_sub(locked, sig), sig - {u})))
        # concrete levels
        deeper_sh = False   # sh always has something pending below it, if it exists with mode
        deeper_dp = (st == 'closed' and not cur)
        for name, lev, deeper in (('sh', sh, deeper_sh), ('dp', dp, deeper_dp)):
            if lev is None:
                continue
            Bup, Aup = fl[name]
            for x in lev:
                k = I.kind[x]
                if Bup and self.minimal(x, lev) and (k != 'A' or deeper):
                    yield ('f', x, upd(**{name: lev - {x}}))
                if Aup and self.maximal(x, lev) and (k != 'B' or deeper):
                    yield ('b', x, upd(**{name: lev - {x}}))
        if st == 'open':
            Bup, Aup = fl['cur']
            for x in cur:
                if x == 'h':
                    continue
                if Bup and self.minimal(x, cur):
                    yield ('f', x, upd(cur=cur - {x}))
                if Aup and self.maximal(x, cur):
                    yield ('b', x, upd(cur=cur - {x}))
            # decompositions
            rem = cur - {'h'}
            pending = sh is not None or bool(locked)
            for trig in ('F', 'K'):
                side = I.Bs if trig == 'F' else I.As      # must be done
                pend = I.As if trig == 'F' else I.Bs      # becomes pending
                m = 'A' if trig == 'F' else 'B'
                if rem & side or mode not in (None, m):
                    continue
                for meth in ('cont', 'stop'):
                    if meth == 'cont' and depth >= self.N:
                        continue
                    nfree, nsh, nlocked, ndp, nmode = free, sh, locked, None, mode
                    if not (rem & pend):
                        if rem & I.Us:
                            nfree = ms_add(free, rem & I.Us)
                        lvl_pending = False
                    else:
                        lvl_pending = True
                    if lvl_pending:
                        if meth == 'stop':
                            ndp = rem
                            nmode = m
                        elif not pending:
                            nsh, nmode = rem, m
                        else:
                            if rem & pend != pend:
                                continue   # cannot happen in a consistent run
                            nlocked = ms_add(locked, rem & I.Us)
                    if meth == 'cont':
                        yield ('d', None, ('open', nmode, nfree, nsh, nlocked, I.P | {'h'}, None,
                                           depth + 1))
                    else:
                        yield ('d', None, ('closed', nmode, nfree, nsh, nlocked, I.S, ndp, depth))
        else:
            # bottom: deeper than every level
            Bup = (mode != 'B') or not (sh is not None or locked or dp is not None)
            Aup = (mode != 'A') or not (sh is not None or locked or dp is not None)
            for s in cur:
                if Bup and all((y, s) not in I.Sorder for y in cur):
                    yield ('f', s, upd(cur=cur - {s}))
                if Aup and all((s, y) not in I.Sorder for y in cur):
                    yield ('b', s, upd(cur=cur - {s}))

    def allow(self, which, h, mv):
        """Hook to restrict the moves of hole `which` (0 = X, 1 = Y)."""
        return True

    def finished(self, h):
        st, mode, free, sh, locked, cur, dp, depth = h
        return st == 'closed' and not cur and sh is None and not locked and dp is None and not free

    def depths(self, one_hole=False):
        I = self.I
        res = set()
        seen = set()
        stack = []
        h0 = ('init', None, (), None, (), None, None, 0)
        hfin = ('closed', None, (), None, (), frozenset(), None, -1)
        for sw in I.states:
            if I.goal <= sw:
                stack.append((I.init, sw, I.T, h0, hfin if one_hole else h0))
        while stack:
            cfg = stack.pop()
            if cfg in seen:
                continue
            seen.add(cfg)
            sf, sb, T, hX, hY = cfg
            if sf == sb and not T and self.finished(hX) and self.finished(hY):
                res.add((hX[7], hY[7]))
            # tnI tasks
            for t in T:
                a = I.lab[t]
                if all((y, t) not in I.Torder for y in T) and I.app(sf, a):
                    stack.append((I.nxt(sf, a), sb, T - {t}, hX, hY))
                if all((t, y) not in I.Torder for y in T):
                    for s in I.pre_states(sb, a):
                        stack.append((sf, s, T - {t}, hX, hY))
            for which in (0, 1):
                h = (hX, hY)[which]
                for mv in self.hole_moves(h, sf, sb):
                    if mv is None or not self.allow(which, h, mv):
                        continue
                    d, x, nh = mv
                    if d == 'f':
                        a = I.lab[x]
                        if not I.app(sf, a):
                            continue
                        nsf, nsbs = I.nxt(sf, a), [sb]
                    elif d == 'b':
                        a = I.lab[x]
                        nsf, nsbs = sf, I.pre_states(sb, a)
                    else:
                        nsf, nsbs = sf, [sb]
                    for nh2 in self.norm(nh):
                        for nsb in nsbs:
                            pair = (nh2, hY) if which == 0 else (hX, nh2)
                            stack.append((nsf, nsb, T) + pair)
        return res


# ------------------------------------------------------------------ random instances
def random_inst(rng):
    facts = ['f%d' % i for i in range(rng.choice([2, 3]))]
    nb, nu, na = rng.choice([1, 2]), rng.choice([0, 1, 2]), rng.choice([1, 2])
    kind = {}
    for i in range(nb):
        kind['b%d' % i] = 'B'
    for i in range(nu):
        kind['u%d' % i] = 'U'
    for i in range(na):
        kind['a%d' % i] = 'A'
    names = list(kind)
    order = set()
    allowed = {('B', 'B'), ('U', 'U'), ('A', 'A'), ('B', 'U'), ('B', 'A'), ('U', 'A')}
    pos = {x: i for i, x in enumerate(names)}
    for x in names:
        for y in names:
            if x != y and pos[x] < pos[y] and (kind[x], kind[y]) in allowed and rng.random() < 0.4:
                order.add((x, y))
    S = ['s0'] if rng.random() < 0.7 else []
    T = ['p%d' % i for i in range(rng.choice([0, 1, 2, 3]))]
    Torder = {(T[i], T[i + 1]) for i in range(len(T) - 1)}
    tasks = names + S + T
    nacts = rng.choice([3, 4, 5])
    acts = {}
    for k in range(nacts):
        pre = frozenset(f for f in facts if rng.random() < 0.3)
        add = frozenset(f for f in facts if rng.random() < 0.35)
        dele = frozenset(f for f in facts if rng.random() < 0.35) - add
        acts['act%d' % k] = (pre, add, dele)
    lab = {t: rng.choice(sorted(acts)) for t in tasks}
    init = frozenset(f for f in facts if rng.random() < 0.5)
    goal = frozenset(f for f in facts if rng.random() < 0.3)
    return Inst(facts, acts, kind, order, S, set(), T, Torder, lab, init, goal)


if __name__ == "__main__":
    seed0 = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    bad_sound = bad_compl = 0
    for seed in range(seed0, seed0 + count):
        rng = random.Random(seed)
        I = random_inst(rng)
        ex = exact_depths(I, N)
        ab = Abs(I, N).depths()
        if ab - ex:
            bad_sound += 1
            print(f"seed {seed}: ABSTRACT TOO STRONG  abstract-only {sorted(ab - ex)}")
        if ex - ab:
            bad_compl += 1
            print(f"seed {seed}: ABSTRACT TOO WEAK    exact-only {sorted(ex - ab)}")
    print(f"done: {count} instances, unsound {bad_sound}, incomplete {bad_compl}")
