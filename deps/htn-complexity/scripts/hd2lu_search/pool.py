"""One hole, left to right, with one stack and a pool of counters.  (HD2_LU.md §6.11)

A hole read left to right needs a stack, but its floating tasks may run while deeper levels are on
top.  Proposal: never modify the stack below its top.

* On the way down push a marker for every level (`b`) and every floating task.
* On the way up, closing a level (`a`) pops its marker and releases the floating-task markers above
  it into a *pool*.  They are earlier than everything already in the pool, so they are prepended.
  Floating tasks executed on the way up are appended.
* The pool is kept as counters of *partial embeddings* `S ⊆ U`: sets of markers reserved for one
  future level.  A prepended marker of type `x` may extend `S` if no `y ∈ S` has `y ≺ x`; an
  appended one if no `y ∈ S` has `x ≺ y`.
* The closing level takes one partial `S` that is down-closed and contains every type ordered
  before an `A`-task.  The rest `U \\ S` is its leftover: it must be completed by appended markers
  before the parent closes.  At most one leftover is pending, so it lives in the finite control.

A floating type not ordered after its level's own `b` may also use the markers between the
parent's marker and the level's own; they are released when the level closes and may extend its
partial only for such types.  `pool_valid` searches the abstract
configurations exactly; `exact_valid` is the semantics (`rich.valid`).  `python3 pool.py N SEED`
compares them on N random words per type.
"""
import random
import sys
from collections import Counter

from rich import Cont, valid


def single_hole(word):
    st, pairs, s = [], [], None
    for i, e in enumerate(word):
        if e == 'b':
            if s is not None:
                return None
            st.append(i)
        elif e == 's':
            if s is not None:
                return None
            s = i
        elif e == 'a':
            if s is None or not st:
                return None
            pairs.append((st.pop(), i))
    if s is None or st:
        return None
    return {'X': (sorted(pairs), s), 'Y': ([], None)}


def exact_valid(word, cont):
    lv = single_hole(word)
    return lv is not None and valid(word, cont, lv)


def pool_valid(word, cont):
    if single_hole(word) is None:
        return False
    U = frozenset(cont.types)
    below = {x: frozenset(p for (p, q) in cont.prec if q == x) for x in U}
    above = {x: frozenset(q for (p, q) in cont.prec if p == x) for x in U}
    # types that must precede an A-task of their level, closed downwards
    need = frozenset(t for t, (ab, ba) in cont.types.items() if ba)
    changed = True
    while changed:
        changed = False
        for t in list(need):
            if not below[t] <= need:
                need = need | below[t]
                changed = True

    early = frozenset(t for t, (ab, ba) in cont.types.items() if not ab)

    def can_prepend(S, x):
        return x not in S and not any(y in S for y in below[x])

    def can_append(S, x):
        return x not in S and not any(y in S for y in above[x])

    def down_closed(S):
        return all(below[x] <= S for x in S)

    def add(pool, S, x, prepend):
        """All pools obtained by putting a marker of type x into the pool."""
        out = [pool + Counter({frozenset([x]): 1})]
        for T in list(pool):
            if (can_prepend if prepend else can_append)(T, x):
                p = pool.copy()
                p[T] -= 1
                if not p[T]:
                    del p[T]
                p[T | {x}] += 1
                out.append(p)
        return out

    def key(stack, pool, left):
        return (stack, frozenset(pool.items()), left)

    seen = set()

    def rec(i, stack, pool, left):
        # left: the pending leftover of the last closed level, as the set of types it already has
        k = (i, key(stack, pool, left))
        if k in seen:
            return False
        seen.add(k)
        if i == len(word):
            return stack == ('H',) and not pool and (left is None or left == U)
        e = word[i]
        if e == 'b':
            return rec(i + 1, stack + ('L',), pool, left)
        if e == 's':
            return rec(i + 1, stack, pool, left)
        if e in U:
            if 's' not in word[:i]:
                return rec(i + 1, stack + (e,), pool, left)
            # on the way up: append to the pool, or to the pending leftover
            if left is not None and can_append(left, e):
                if rec(i + 1, stack, pool, left | {e}):
                    return True
            return any(rec(i + 1, stack, p, left) for p in add(pool, None, e, False))
        if e == 'a':
            if left is not None and left != U:
                return False                    # the child's leftover is overdue
            # release the markers above the top level marker, latest first (= prepend)
            st = list(stack)
            rel = []
            while st[-1] not in 'LH':
                rel.append(st.pop())
            if st[-1] == 'H':
                return False
            st.pop()
            # markers between the parent's marker and this one: usable by this level only for
            # types whose window starts at the parent's b
            reg = []
            j = len(st)
            while st[j - 1] not in 'LH':
                j -= 1
                reg.append(st[j])
            rest = tuple(st[:j])
            pools = [pool]
            for x in rel:
                pools = [q for p in pools for q in add(p, None, x, True)]
            for p in pools:
                cands = [(S, True) for S in p] + [(frozenset(), False)]
                for S, from_pool in cands:
                    q = p.copy()
                    if from_pool:
                        q[S] -= 1
                        if not q[S]:
                            del q[S]
                    # now release the region below, extending S by early types only
                    opts = [(q, S)]
                    for x in reg:
                        nxt = []
                        for (qq, SS) in opts:
                            nxt += [(r, SS) for r in add(qq, None, x, True)]
                            if x in early and can_prepend(SS, x):
                                nxt.append((qq, SS | {x}))
                        opts = nxt
                    for (qq, SS) in opts:
                        if need <= SS and down_closed(SS):
                            if rec(i + 1, rest, qq, SS):
                                return True
            return False
        return rec(i + 1, stack, pool, left)

    return rec(0, ('H',), Counter(), None)       # H: the start of the hole


TESTS = {
    'u0<v|ba': Cont({'u': (False, True), 'v': (True, True)}, {('u', 'v')}),
    'u0|a,v0': Cont({'u': (False, True), 'v': (False, False)}),
    'v|b<u0|a': Cont({'u': (False, True), 'v': (True, False)}, {('v', 'u')}),
    'u0<v0<w|b': Cont({'u': (False, False), 'v': (False, True), 'w': (True, False)},
                      {('u', 'v'), ('v', 'w'), ('u', 'w')}),
    'u<v|ba': Cont({'u': (True, True), 'v': (True, True)}, {('u', 'v')}),
    'u|ba<v|b': Cont({'u': (True, True), 'v': (True, False)}, {('u', 'v')}),
    'u|b<v|ba': Cont({'u': (True, False), 'v': (True, True)}, {('u', 'v')}),
    'u,v<w|ba': Cont({'u': (True, True), 'v': (True, True), 'w': (True, True)},
                     {('u', 'w'), ('v', 'w')}),
    'u<v,w|b': Cont({'u': (True, False), 'v': (True, True), 'w': (True, False)},
                    {('u', 'v'), ('u', 'w')}),
    'u<v<w': Cont({'u': (True, True), 'v': (True, False), 'w': (True, True)},
                  {('u', 'v'), ('v', 'w'), ('u', 'w')}),
}


def random_word(rng, cont, n):
    """A single hole of depth n with each floating task placed somewhere (valid or not)."""
    sk = ['b'] * n + ['s'] + ['a'] * n
    w = list(sk)
    for _ in range(n):
        for t in cont.types:
            w.insert(rng.randint(0, len(w)), t)
    return ''.join(w)


if __name__ == "__main__":
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
    for name, c in TESTS.items():
        agree = disagree = pos = 0
        for _ in range(count):
            w = random_word(rng, c, rng.randint(1, 4))
            a, b = exact_valid(w, c), pool_valid(w, c)
            pos += a
            if a == b:
                agree += 1
            else:
                disagree += 1
                print('  MISMATCH', name, w, 'exact', a, 'pool', b)
        print(name, 'agree', agree, 'disagree', disagree, 'valid', pos, flush=True)
