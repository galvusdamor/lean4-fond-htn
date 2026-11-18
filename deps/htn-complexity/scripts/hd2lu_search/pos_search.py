"""Positional variant of abs_search.Abs: `locked` is an ordered tuple (oldest first); the shallow
end releases locked[0], the deep end takes locked[-1].  Optional bound L on len(locked)."""
import abs_search as A

class Pos(A.Abs):
    def __init__(self, I, N, L=None):
        super().__init__(I, N)
        self.L = L

    def norm(self, h):
        I = self.I
        st, mode, free, sh, locked, cur, dp, depth = h
        free = tuple((s, n) for s, n in free if s)
        if self.L is not None and len(locked) > self.L:
            return []
        if mode is None:
            return [(st, mode, free, sh, locked, cur, dp, depth)]
        P = self.pend(mode)
        if sh is not None and not (sh & P):
            if sh & I.Us:
                free = A.ms_add(free, sh & I.Us)
            sh = None
            if locked:
                return self.norm((st, mode, free, P | locked[0], locked[1:], cur, dp, depth))
        if sh is None and not locked and dp is not None and not (dp & P):
            if dp & I.Us:
                free = A.ms_add(free, dp & I.Us)
            dp = None
        if st == 'closed' and dp is not None and not cur and not dp:
            if locked:
                return self.norm((st, mode, free, sh, locked[:-1], cur, P | locked[-1], depth))
            elif sh is not None:
                return self.norm((st, mode, free, None, locked, cur, sh, depth))
            else:
                dp = None
        if not (sh is not None or locked or dp is not None):
            mode = None
        return [(st, mode, tuple((s, n) for s, n in free if s), sh, locked, cur, dp, depth)]

    def hole_moves(self, h, sf, sb):
        st, mode, free, sh, locked, cur, dp, depth = h
        # translate the ordered tuple to the multiset interface for moves, then back
        for mv in super().hole_moves((st, mode, free, sh, (), cur, dp, depth), sf, sb):
            if mv is None:
                continue
            d, x, nh = mv
            nst, nmode, nfree, nsh, nlocked, ncur, ndp, ndepth = nh
            # a decomposition may have appended one locked piece (multiset of size 1)
            app = tuple(s for s, n in nlocked for _ in range(n))
            yield (d, x, (nst, nmode, nfree, nsh, locked + app, ncur, ndp, ndepth))
        # progress / regress inside a locked piece (by position)
        fl = self.flags(h)
        Bup, Aup = fl['locked']
        I = self.I
        for i, sig in enumerate(locked):
            for u in sig:
                nl = locked[:i] + (sig - {u},) + locked[i + 1:]
                if Bup and self.minimal(u, sig | (I.Bs if mode == 'B' else frozenset())):
                    yield ('f', u, (st, mode, free, sh, nl, cur, dp, depth))
                if Aup and self.maximal(u, sig | (I.As if mode == 'A' else frozenset())):
                    yield ('b', u, (st, mode, free, sh, nl, cur, dp, depth))
