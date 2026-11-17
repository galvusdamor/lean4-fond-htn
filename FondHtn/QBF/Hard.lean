import FondHtn.QBF.SavitchPT
import FondHtn.QBF.ToFondPT
/-!
# [CB21, Thm. 5.1], hardness (repaired): primitive strong OD plan existence is PSPACE-hard

**Deviation from [CB21].**  The published proof reduces from `(m, n, k)`-games (k-in-a-row) and
is incorrect (catalogue G9).  We reduce from TQBF instead:

1. `FOND.QBF.tqbf_pspaceHard` — TQBF (prenex QBF with a CNF matrix, `FOND.QBF.TQBF`) is
   PSPACE-hard, by Savitch's construction from STRIPS plan existence
   (`FOND.QBF.strips_redP_tqbf`; STRIPS is PSPACE-hard by Bylander,
   `HTN.Article.strips_pspaceHard`);
2. `FOND.QBF.tqbf_redP_strongOD_PRIM` — TQBF reduces to strong OD plan existence of primitive
   (partially ordered) problems, with existential gadgets (two unordered tasks, the last one
   executed fixes the value), universal gadgets (nondeterministic tasks), block ordering, and a
   check phase (`FOND.QBF.ToFond`).  The constructed problems use **no negative preconditions**
   and actions with at most two effects, so they lie in the fragment of [CB21].

* **`FOND.strongOD_PRIM_pspaceHard`** — `PlanExFM strongOD PRIM` is PSPACE-hard.
-/

namespace FOND

/-- **[CB21, Thm. 5.1], hardness** (repaired via TQBF): strong OD plan existence of primitive
problems is PSPACE-hard. -/
theorem strongOD_PRIM_pspaceHard : HTN.Cx.Hard HTN.Cx.PSPACE (PlanExFM .strongOD FClass.PRIM) :=
  QBF.tqbf_pspaceHard.of_redP QBF.tqbf_redP_strongOD_PRIM

end FOND
