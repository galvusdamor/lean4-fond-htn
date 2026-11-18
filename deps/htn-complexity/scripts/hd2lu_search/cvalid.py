"""ctypes wrapper of cmatch.c: `cvalid(word, cont, lv)` is `rich.valid`, in C.  (HD2_LU.md §6.13)

The shared library is built on first use into the directory given by $CMATCH_DIR (default: this
directory)."""
import ctypes
import os
import subprocess

from rich import edf, windows

_here = os.path.dirname(os.path.abspath(__file__))
_dir = os.environ.get('CMATCH_DIR', _here)
_so = os.path.join(_dir, 'cmatch.so')
if not os.path.exists(_so):
    subprocess.check_call(['cc', '-O2', '-shared', '-fPIC', '-o', _so, os.path.join(_here, 'cmatch.c')])
_lib = ctypes.CDLL(_so)
_lib.valid.restype = ctypes.c_int
I = ctypes.POINTER(ctypes.c_int)
U = ctypes.POINTER(ctypes.c_uint64)
_lib.valid.argtypes = [ctypes.c_int, I, I, I, U, ctypes.c_int, I, I, ctypes.c_long]


def _components(cont):
    comp = {t: {t} for t in cont.types}
    for a, b in cont.prec:
        merged = comp[a] | comp[b]
        for t in merged:
            comp[t] = merged
    return {frozenset(c) for c in comp.values()}


def cvalid(word, cont, lv, max_steps=10_000_000):
    """Types not related by the in-level order are matched independently: a single type by
    earliest-deadline-first (exact for interval windows), a component of ordered types by the
    C backtracking matcher."""
    slots_all = windows(word, cont, lv)
    for comp in _components(cont):
        slots = [s for s in slots_all if s[1] in comp]
        if len(comp) == 1:
            (t,) = comp
            if not edf(word, t, slots):
                return False
        elif not _cvalid(word, cont, slots, comp, max_steps):
            return False
    return True


def _cvalid(word, cont, slots, comp, max_steps):
    ex = [(i, e) for i, e in enumerate(word) if e in comp]
    if len(ex) != len(slots):
        return False
    tid = {t: k for k, t in enumerate(sorted(comp))}
    index = {(lvl, t): s for s, (lvl, t, lo, hi) in enumerate(slots)}
    n = len(slots)
    lo = (ctypes.c_int * n)(*[s[2] for s in slots])
    hi = (ctypes.c_int * n)(*[s[3] for s in slots])
    ty = (ctypes.c_int * n)(*[tid[s[1]] for s in slots])
    pr = (ctypes.c_uint64 * n)(*[sum(1 << index[(s[0], p)] for p in cont.preds[s[1]] if p in comp)
                                for s in slots])
    xp = (ctypes.c_int * len(ex))(*[i for i, e in ex])
    xt = (ctypes.c_int * len(ex))(*[tid[e] for i, e in ex])
    r = _lib.valid(n, lo, hi, ty, pr, len(ex), xp, xt, max_steps)
    if r < 0:
        raise RuntimeError('matcher budget exhausted')
    return bool(r)
