import time
import abs_search as A, cut_search as CS, hand_instances as H
I = H.CEX
print("exact", sorted(A.exact_depths(I, 2)), flush=True)
for K in (0, 1):
    t = time.time()
    print(f"K={K}", sorted(CS.depths(I, 2, K)), f"{time.time()-t:.0f}s", flush=True)
