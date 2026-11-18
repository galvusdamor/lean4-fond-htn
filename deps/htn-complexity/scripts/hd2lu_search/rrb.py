"""Can a STRIPS state force a thick bubble?  (HD2_LU.md §6.12)

A STRIPS state is determined by, for every fact, the last action that touched it.  So the state
after a plan depends only on the *last-occurrence order* of its actions (its image in the free
right regular band: `xx = x`, `xyx = yx`).  Whether the next action is applicable depends only on
that order.

Given a plan `w0`, the most restrictive STRIPS-like constraint containing it allows exactly the
steps `(order of the prefix, next action)` that occur along `w0`, with the goal "final order as
in `w0`".  `closure_words` enumerates the words of that language (abstract model of `rich.py`,
bounded depth) that have a valid interpretation, with their least width.

    python3 rrb.py WORD MAXDEPTH          # floating types u, v, w, z as in the forced plan
"""
import sys

from rich import Cont, interpretations, valid
from width import min_width

FOUR = Cont({'u': (True, True), 'v': (True, False), 'w': (False, True), 'z': (False, False)})


def lo_order(order, x):
    return tuple(y for y in order if y != x) + (x,)


def allowed_steps(w0):
    steps, order = set(), ()
    for x in w0:
        steps.add((order, x))
        order = lo_order(order, x)
    return steps, order


def closure_words(w0, cont, maxdepth, maxlen=None):
    steps, final = allowed_steps(w0)
    maxlen = maxlen or len(w0) + 6
    found = []

    def rec(word, order, nb, na, ns):
        # prune: depth bound and HTN counts (one task of each type per level)
        if nb > maxdepth or na > nb:
            return
        if len(word) > maxlen:
            return
        if order == final and ns == 2 and na == nb and word:
            if all(word.count(t) == nb for t in cont.types):
                found.append(word)
        for x in sorted({x for (o, x) in steps if o == order}):
            if x == 's' and ns >= 2:
                continue
            if x in cont.types and word.count(x) >= maxdepth:
                continue
            rec(word + x, lo_order(order, x), nb + (x == 'b'), na + (x == 'a'), ns + (x == 's'))

    rec('', (), 0, 0, 0)
    res = []
    for w in found:
        vals = [lv for lv in interpretations(w) if valid(w, cont, lv)]
        if vals:
            res.append((min(min_width(w, lv) for lv in vals), w, len(vals)))
    return sorted(res)


if __name__ == "__main__":
    w0, maxdepth = sys.argv[1], int(sys.argv[2])
    res = closure_words(w0, FOUR, maxdepth)
    from collections import Counter
    print('valid words in the closure:', len(res), Counter(r[0] for r in res))
    for r in res[:5]:
        print(' ', r)
