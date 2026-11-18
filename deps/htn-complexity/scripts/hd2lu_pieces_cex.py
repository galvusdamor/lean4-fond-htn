"""Brute-force check of the H2 ∩ L instance of HD2_LU.md §4 (formalised in
HtnComplexity/HDDecide/HD2LUCex.lean): solvable, but not solvable by the bidirectional search on
pieces of Dekker and Behnke (Lemma 6 / Prop. 7).

    cont = {b ≺ h ≺ a}, stop = {t}, t0 = {c1, c2, p1 ≺ p2 ≺ p3}
    phases 0 | 1 | 2 | 3:  b in 0, 1;  a in 2, 3;  t in 0, 3;  p2 needs a b in 1, p3 an a in 2

Usage: python3 hd2lu_pieces_cex.py [control]
  control: let t run in every phase; then the search on pieces must succeed.
"""
import itertools
import sys
from collections import Counter
from functools import lru_cache

FACTS = ["bOK", "aOK", "tOK", "bDone", "aDone"]
ACT = {  # name: (pre, add, del)
    "b": ({"bOK"}, {"bDone"}, set()),
    "a": ({"aOK"}, {"aDone"}, set()),
    "t": ({"tOK"}, set(), set()),
    "p1": (set(), set(), {"tOK", "bDone"}),
    "p2": ({"bDone"}, {"aOK"}, {"bOK", "aDone"}),
    "p3": ({"aDone"}, {"tOK"}, set()),
}
INIT = frozenset({"bOK", "tOK"})
ALLSTATES = [frozenset(c) for r in range(len(FACTS) + 1) for c in itertools.combinations(FACTS, r)]


def app(s, x):
    return ACT[x][0] <= s


def nxt(s, x):
    pre, add, dele = ACT[x]
    return frozenset((s - dele) | add)


def closure(pairs):
    rel = set(pairs)
    while True:
        new = {(x, z) for (x, y) in rel for (y2, z) in rel if y == y2} - rel
        if not new:
            return frozenset(rel)
        rel |= new


# task networks: ids -> label ('C' = compound), strict order (transitive)
NETS = {
    0: ({"c1": "C", "c2": "C", "p1": "p1", "p2": "p2", "p3": "p3"},
        closure({("p1", "p2"), ("p2", "p3")})),
    1: ({"b": "b", "h": "C", "a": "a"}, closure({("b", "h"), ("h", "a")})),
    2: ({"t": "t"}, frozenset()),
}
METHODS = [1, 2]  # cont, stop — both decompose the single compound name


def plan_exists(n1, n2):
    """Plan existence for the unrolled primitive network N(n1, n2), by search over downsets."""
    lab, ordp = {("t0", 0, p): p for p in ("p1", "p2", "p3")}, set()
    ordp |= {(("t0", 0, "p1"), ("t0", 0, "p2")), (("t0", 0, "p2"), ("t0", 0, "p3"))}
    for hole, n in (("X", n1), ("Y", n2)):
        for k in range(1, n + 1):
            lab[(hole, k, "b")], lab[(hole, k, "a")] = "b", "a"
        lab[(hole, n + 1, "t")] = "t"
        for k in range(1, n + 1):
            for y in [y for y in lab if y[0] == hole and y[1] > k]:
                ordp |= {((hole, k, "b"), y), (y, (hole, k, "a"))}
            ordp.add(((hole, k, "b"), (hole, k, "a")))
    ordp = closure(ordp)
    tasks = frozenset(lab)
    preds = {t: {x for (x, y) in ordp if y == t} for t in tasks}

    @lru_cache(maxsize=None)
    def go(done, s):
        if done == tasks:
            return ()
        for t in sorted(tasks - done):
            if preds[t] <= done and app(s, lab[t]):
                r = go(done | {t}, nxt(s, lab[t]))
                if r is not None:
                    return (lab[t],) + r
        return None

    return go(frozenset(), INIT)


def pieces_solvable(max_dec):
    """The search on pieces (HTN.HD.HStep) with at most `max_dec` decompositions."""
    seen, stack = set(), []
    for sw in ALLSTATES:  # guessed final state (no goal)
        stack.append((INIT, sw, frozenset(Counter({(0, frozenset(NETS[0][0])): 1}).items()), 0))
    while stack:
        cfg = stack.pop()
        if cfg in seen:
            continue
        seen.add(cfg)
        sf, sb, pcs, dec = cfg
        M = Counter(dict(pcs))
        if not M and sf == sb:
            return True
        for (k, S) in list(M):
            lab, ordk = NETS[k]
            for x in S:
                M2 = M.copy()
                M2[(k, S)] -= 1
                if M2[(k, S)] == 0:
                    del M2[(k, S)]
                if S - {x}:
                    M2[(k, S - {x})] += 1
                minimal = all((y, x) not in ordk for y in S)
                maximal = all((x, y) not in ordk for y in S)
                if lab[x] == "C":
                    if minimal and maximal and dec < max_dec:
                        for m in METHODS:
                            M3 = M2.copy()
                            M3[(m, frozenset(NETS[m][0]))] += 1
                            stack.append((sf, sb, frozenset(M3.items()), dec + 1))
                    continue
                if minimal and app(sf, lab[x]):
                    stack.append((nxt(sf, lab[x]), sb, frozenset(M2.items()), dec))
                if maximal:
                    for s in ALLSTATES:
                        if app(s, lab[x]) and nxt(s, lab[x]) == sb:
                            stack.append((sf, s, frozenset(M2.items()), dec))
    return False


if __name__ == "__main__":
    if sys.argv[1:] == ["control"]:
        ACT["t"] = (set(), set(), set())
    for n in [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2)]:
        p = plan_exists(*n)
        print(f"N{n} solvable: {p is not None}", "" if p is None else " ".join(p))
    for K in range(0, 9):
        ok = pieces_solvable(K)
        print(f"search on pieces with ≤ {K} decompositions: {'SUCCESS' if ok else 'no'}")
        if ok:
            break
