"""Multi-cut isolated search for 2-HD ∩ L instances (HD2_LU.md §6.7).

The plan is cut into K+1 segments; segment i is searched by a forward frontier F_i (from its
start) and a backward frontier B_i (from its end).  Classes order the plan positions:
F_0 < B_0 < F_1 < B_1 < …  (class 2i = F_i, 2i+1 = B_i).  Only isolated compound tasks are
decomposed; a child piece inherits bounds [lo, hi] on the classes of its tasks from the classes
of its parent's B- and A-tasks.  States at the cuts are guessed.

depths(I, N, K): the set of (n1, n2) with n1, n2 <= N for which the search finds a solution.
"""
import itertools
from collections import Counter


class CutSearch:
    def __init__(self, I, N, K):
        self.I, self.N, self.K = I, N, K
        self.top = 2 * K + 1
        self._nb = {}
        # nets: 0 = initial network, 1 = cont, 2 = stop
        I_ = I
        self.nets = {
            0: (I_.T | {'c1', 'c2'}, I_.Torder, {**{t: I_.lab[t] for t in I_.T}, 'c1': None, 'c2': None}),
            1: (I_.P | {'h'}, I_.order, {**{x: I_.lab[x] for x in I_.P}, 'h': None}),
            2: (I_.S, I_.Sorder, {s: I_.lab[s] for s in I_.S}),
        }

    # piece = (net, hole, rem, proc, lo, hi);  proc = frozenset of (task, class)
    def preds(self, k, x):
        key = (k, x, 'p')
        if key not in self._nb:
            self._nb[key] = frozenset(y for (y, z) in self.nets[k][1] if z == x)
        return self._nb[key]

    def succs(self, k, x):
        key = (k, x, 's')
        if key not in self._nb:
            self._nb[key] = frozenset(z for (y, z) in self.nets[k][1] if y == x)
        return self._nb[key]

    def can(self, piece, x, c):
        k, hole, rem, proc, lo, hi = piece
        if not (lo <= c <= hi):
            return False
        pc = dict(proc)
        if c % 2 == 0:   # forward F_i
            for y in self.preds(k, x):
                if y in rem or pc[y] > c:
                    return False
            for y in self.succs(k, x):
                if y not in rem and pc[y] <= c:
                    return False
        else:            # backward B_i
            for y in self.succs(k, x):
                if y in rem or pc[y] < c:
                    return False
            for y in self.preds(k, x):
                if y not in rem and pc[y] >= c:
                    return False
        return True

    def child_bounds(self, piece, x):
        """Class bounds for the children of the isolated compound task x of `piece`."""
        k, hole, rem, proc, lo, hi = piece
        pc = dict(proc)
        nlo, nhi = lo, hi
        for y in self.preds(k, x):
            c = pc[y]
            nlo = max(nlo, c if c % 2 == 0 else c + 1)
        for y in self.succs(k, x):
            c = pc[y]
            nhi = min(nhi, c if c % 2 == 1 else c - 1)
        return nlo, nhi

    def prune(self, k, rem, proc):
        """Keep the class of a processed task only while a neighbour in the piece is unprocessed."""
        return frozenset((y, c) for (y, c) in proc
                         if any(z in rem for z in self.preds(k, y) | self.succs(k, y)))

    def initial(self):
        I = self.I
        tn0 = (0, -1, frozenset(self.nets[0][0]), frozenset(), 0, self.top)
        for guesses in itertools.product(I.states, repeat=self.K):
            for sw in I.states:
                if not I.goal <= sw:
                    continue
                sf = (I.init,) + guesses
                sb = guesses + (sw,)
                yield (sf, sb, Counter({tn0: 1}), (0, 0))

    def freeze(self, sf, sb, M, d):
        return (sf, sb, frozenset((p, n) for p, n in M.items() if n > 0), d)

    def solved_depths(self):
        I = self.I
        res, seen, stack = set(), set(), []
        for sf, sb, M, d in self.initial():
            stack.append(self.freeze(sf, sb, M, d))
        while stack:
            cfg = stack.pop()
            if cfg in seen:
                continue
            seen.add(cfg)
            sf, sb, pcs, d = cfg
            M = Counter(dict(pcs))
            if not M and all(sf[i] == sb[i] for i in range(self.K + 1)):
                res.add(d)
                continue
            for piece in list(M):
                k, hole, rem, proc, lo, hi = piece
                labs = self.nets[k][2]
                M1 = M.copy()
                M1[piece] -= 1
                for x in rem:
                    if labs[x] is None:
                        # compound: decompose if isolated
                        if any(y in rem for y in self.preds(k, x) | self.succs(k, x)):
                            continue
                        nlo, nhi = self.child_bounds(piece, x)
                        if nlo > nhi:
                            continue
                        nrem = rem - {x}
                        M2 = M1.copy()
                        if nrem:
                            M2[(k, hole, nrem, self.prune(k, nrem, proc), lo, hi)] += 1
                        h = hole if hole >= 0 else (0 if x == 'c1' else 1)
                        for meth in (1, 2):
                            if meth == 1 and d[h] >= self.N:
                                continue
                            M3 = M2.copy()
                            child = (meth, h, frozenset(self.nets[meth][0]), frozenset(), nlo, nhi)
                            if child[2]:
                                M3[child] += 1
                            nd = (d[0] + (meth == 1 and h == 0), d[1] + (meth == 1 and h == 1))
                            stack.append(self.freeze(sf, sb, M3, nd))
                        continue
                    a = labs[x]
                    for c in range(lo, hi + 1):
                        if not self.can(piece, x, c):
                            continue
                        i = c // 2
                        nrem = rem - {x}
                        nproc = self.prune(k, nrem, proc | {(x, c)})
                        M2 = M1.copy()
                        if nrem:
                            M2[(k, hole, nrem, nproc, lo, hi)] += 1
                        if c % 2 == 0:
                            if not I.app(sf[i], a):
                                continue
                            nsf = sf[:i] + (I.nxt(sf[i], a),) + sf[i + 1:]
                            stack.append(self.freeze(nsf, sb, M2, d))
                        else:
                            for s in I.pre_states(sb[i], a):
                                nsb = sb[:i] + (s,) + sb[i + 1:]
                                stack.append(self.freeze(sf, nsb, M2, d))
        return res


def depths(I, N, K):
    return CutSearch(I, N, K).solved_depths()
