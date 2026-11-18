"""Random generator of small 2-HD ∩ L instances with floating tasks and a phase chain."""
import random, sys, time
import abs_search as A

def hard_inst(rng):
    facts = ['f0', 'f1', 'f2']
    kind = {'b0': 'B', 'u0': 'U', 'a0': 'A'}
    if rng.random() < 0.5: kind['u1'] = 'U'
    if rng.random() < 0.3: kind['b1'] = 'B'
    if rng.random() < 0.3: kind['a1'] = 'A'
    names = list(kind)
    allowed = {('B','B'),('U','U'),('A','A'),('B','U'),('B','A'),('U','A')}
    pos = {x: i for i, x in enumerate(names)}
    order = {(x, y) for x in names for y in names
             if x != y and pos[x] < pos[y] and (kind[x], kind[y]) in allowed and rng.random() < 0.5}
    S = ['s0']
    T = ['p%d' % i for i in range(rng.choice([2, 3]))]
    Torder = {(T[i], T[i+1]) for i in range(len(T) - 1)}
    acts = {}
    for k in range(rng.choice([4, 5, 6])):
        pre = frozenset(f for f in facts if rng.random() < 0.35)
        add = frozenset(f for f in facts if rng.random() < 0.35)
        dele = frozenset(f for f in facts if rng.random() < 0.35) - add
        acts['act%d' % k] = (pre, add, dele)
    lab = {t: rng.choice(sorted(acts)) for t in names + S + T}
    init = frozenset(f for f in facts if rng.random() < 0.5)
    goal = frozenset(f for f in facts if rng.random() < 0.3)
    return A.Inst(facts, acts, kind, order, S, set(), T, Torder, lab, init, goal)

