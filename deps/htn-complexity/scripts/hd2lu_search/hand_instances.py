"""Hand instances for HD2_LU.md §6.5.

* the formalised counterexample (HD2LUCex.lean): solvable at depth (1,1); the early-decomposition
  search finds it (the search on pieces does not);
* a one-hole 1-HD ∩ L instance with no plan at any depth, on which the *counting* abstraction of
  locked U-pieces finds a fake plan of depth 4, while the positional search is exact.

Usage: python3 hand_instances.py
"""
import abs_search as A
import pos_search as PS

# --- the formalised counterexample
# The formalised counterexample (HD2LUCex.lean) as an Inst: must be solvable at depth (1,1),
# and the abstract early-decomposition search must find it.
F = ['bOK', 'aOK', 'tOK', 'bDone', 'aDone']
acts = {'b': (frozenset({'bOK'}), frozenset({'bDone'}), frozenset()),
        'a': (frozenset({'aOK'}), frozenset({'aDone'}), frozenset()),
        't': (frozenset({'tOK'}), frozenset(), frozenset()),
        'P1': (frozenset(), frozenset(), frozenset({'tOK', 'bDone'})),
        'P2': (frozenset({'bDone'}), frozenset({'aOK'}), frozenset({'bOK', 'aDone'})),
        'P3': (frozenset({'aDone'}), frozenset({'tOK'}), frozenset())}
kind = {'b0': 'B', 'a0': 'A'}
lab = {'b0': 'b', 'a0': 'a', 's0': 't', 'p0': 'P1', 'p1': 'P2', 'p2': 'P3'}
CEX = A.Inst(F, acts, kind, set(), ['s0'], set(), ['p0', 'p1', 'p2'], {('p0', 'p1'), ('p1', 'p2')},
           lab, {'bOK', 'tOK'}, set())

# --- the one-hole fake for the counting abstraction
"""Hand-made 1-HD ∩ L instance on which the counting abstraction (free choice of the locked
piece at deep-end move-up) finds a fake solution.  cont = b < u < a (u floats w.r.t. h),
stop = {} ; phases 0a 0b 1a 1b 1c 1d 2 via a chain p1..p6.
Valid plans are impossible: >= 2 b's in phase 1 and >= 2 a's in phase 1 force two levels inside
phase 1, which need two u's there, but only one u fits (in 1b)."""

F = ['uOK', 'uPh', 'bPh', 'aPh', 'bDone', 'aDone']
fs = frozenset
acts = {
    'b': (fs({'bPh'}), fs({'bDone'}), fs()),
    'u': (fs({'uOK', 'uPh'}), fs(), fs({'uOK'})),
    'a': (fs({'aPh'}), fs({'aDone'}), fs()),
    # 0a -> 0b: refill uOK
    'P1': (fs(), fs({'uOK'}), fs()),
    # 0b -> 1a: no u, clear bDone
    'P2': (fs(), fs(), fs({'uPh', 'bDone'})),
    # 1a -> 1b: needs a b in 1a; one u allowed
    'P3': (fs({'bDone'}), fs({'uOK', 'uPh'}), fs({'bDone'})),
    # 1b -> 1c: needs a b in 1b; no b, no u; a allowed
    'P4': (fs({'bDone'}), fs({'aPh'}), fs({'bPh', 'uPh', 'aDone'})),
    # 1c -> 1d: needs an a in 1c
    'P5': (fs({'aDone'}), fs(), fs({'aDone'})),
    # 1d -> 2: needs an a in 1d; u allowed again (one)
    'P6': (fs({'aDone'}), fs({'uOK', 'uPh'}), fs()),
}
kind = {'b0': 'B', 'u0': 'U', 'a0': 'A'}
order = {('b0', 'u0'), ('u0', 'a0')}
T = ['p1', 'p2', 'p3', 'p4', 'p5', 'p6']
lab = {'b0': 'b', 'u0': 'u', 'a0': 'a', **{f'p{i}': f'P{i}' for i in range(1, 7)}}
FAKE = A.Inst(F, acts, kind, order, [], set(), T, {(T[i], T[i + 1]) for i in range(5)}, lab,
           {'uOK', 'uPh', 'bPh'}, set())



if __name__ == "__main__":
    print("counterexample   exact", sorted(A.exact_depths(CEX, 2)),
          "| positional", sorted(PS.Pos(CEX, 2).depths()))
    print("fake (one hole)  exact", [n for n in range(6) if A.exact_solvable(FAKE, n, -1)],
          "| counting", sorted(d[0] for d in A.Abs(FAKE, 5).depths(one_hole=True)),
          "| positional", sorted(d[0] for d in PS.Pos(FAKE, 5).depths(one_hole=True)))
