import random, sys, time
import abs_search as A, iso_search as IS, gen_hard as G
seed0, count, N = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
bad = mixed = 0
for seed in range(seed0, seed0 + count):
    I = G.hard_inst(random.Random(seed))
    t = time.time()
    ex = A.exact_depths(I, N)
    iso = IS.depths_one_isolated(I, N)
    allp = {(a, b) for a in range(N + 1) for b in range(N + 1)}
    mixed += ex not in (set(), allp)
    tag = "OK" if ex == iso else "MISMATCH"
    if ex != iso:
        bad += 1
    print(f"seed {seed} {tag} exact={sorted(ex)} iso={sorted(iso)} {time.time()-t:.0f}s", flush=True)
print(f"done {count}: mismatches {bad}, non-trivial {mixed}", flush=True)
