"""Positional search in which hole X (index 0) decomposes only *isolated* holes (Lemma 6 style:
its B- and A-blocks of the level are done), while hole Y may decompose early."""
import pos_search as PS


class IsoX(PS.Pos):
    def allow(self, which, h, mv):
        if which != 0 or mv[0] != 'd' or h[0] != 'open':
            return True
        cur = h[5]
        return not (cur & (self.I.Bs | self.I.As))


def depths_one_isolated(I, N):
    """Depth pairs found when one of the two (symmetric) holes is isolated."""
    d = IsoX(I, N).depths()
    return d | {(b, a) for (a, b) in d}
