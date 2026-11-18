"""Search u-placements on a zig-zag skeleton for ones forcing many cuts (lower bound)."""
import random, sys, time
import forcing as F

def place(skel, gaps):
    """Insert one u into each listed gap index (gap g = before skeleton position g)."""
    out = []
    for g in range(len(skel) + 1):
        out += ['u'] * gaps.count(g)
        if g < len(skel):
            out.append(skel[g])
    return ''.join(out)

skel = sys.argv[1]
nlev = skel.count('b')
trials = int(sys.argv[2])
rng = random.Random(int(sys.argv[3]))
best = (-1, None)
t0 = time.time()
for _ in range(trials):
    gaps = sorted(rng.randint(1, len(skel) - 1) for _ in range(nlev))
    seq = place(skel, gaps)
    k, valid = F.cuts_lb(seq, kmax=3)
    if valid and k is not None and k > best[0]:
        best = (k, seq)
        print(f"new best {k} valid={valid} {seq} ({time.time()-t0:.0f}s)", flush=True)
print("best", best)
