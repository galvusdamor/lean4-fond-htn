import random, sys, time
import abs_search as A, iso_search as IS
import hand_instances as H
print("counterexample  exact", sorted(A.exact_depths(H.CEX, 2)),
      "| one hole isolated", sorted(IS.depths_one_isolated(H.CEX, 2)), flush=True)
