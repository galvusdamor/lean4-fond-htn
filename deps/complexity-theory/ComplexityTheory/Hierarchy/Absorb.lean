import ComplexityTheory.Hierarchy.Collapse
/-!
# A guard: a base class that absorbs one quantifier collapses the hierarchy

The cells of Table 3 that rest on the non-collapse of the hierarchy of a scale
(`HtnCompilability/Space/Table3Weak.lean`) need, besides the separation, an *interface* whose
source side is

> the source planning class has a polynomial-time hardness family for **every `Σ₁` language of
> the scale**.

It is tempting to discharge that side with the hardness families the development already has —
`HTN.Space.apSpaceHardSource` and `HTN.Space.apSpaceHardSourceAC`, which cover every language of
alternating polynomial space, i.e. of the *base* class of the intended exponential scale.  This
file is the proof that the temptation must be resisted: **if the base class of a scale answers
the existential question of each of its own relations, the hierarchy of the scale collapses**,
the separation hypothesis of the cells is false, and the cell theorems obtained that way are
vacuous.

So the source side of the interface has to sit one quantifier above the base class — at the
exponential scale, at `NEXPTIME` rather than at `EXPTIME` — and no re-reading of the existing
`EXPTIME`-level families supplies it.

## Main definitions and results

* `HTN.Hier.AbsorbEx` — the base class absorbs one existential quantifier, with parameters;
* `HTN.Hier.blockBase_of_absorbEx` — every quantifier block, with parameters, is then a base
  relation;
* `HTN.Hier.collapseAt_zero_of_absorbEx` — the hierarchy collapses to its base class;
* `HTN.Hier.collapseAt_two_of_absorbEx` — hence to level `2`, which is what the cells' separation
  denies.
-/

namespace HTN

namespace Hier

variable {s : Scale}

/-- **The base class absorbs one existential quantifier.**  For every base relation, the question
"is there an admissible string extending the parameters that satisfies it?" — `HTN.Hier.ExQ` — is
again a base relation.

At the exponential scale this says `NEXPTIME ⊆ EXPTIME`, which is exactly what the hardness
families of the development's `EXPTIME` level would have to supply were they to serve as the
source side of the interface of cells 3–5. -/
def AbsorbEx (s : Scale) : Prop :=
  ∀ R, s.base R → s.base fun x ws => ExQ s R x ws

/-- **Every quantifier block, with parameters, is a base relation** — by induction on the length
of the prefix, the existential step by absorption and the universal step by complementation. -/
theorem blockBase_of_absorbEx (hcompl : ∀ R, s.base R → s.base (notRel R)) (habs : AbsorbEx s) :
    ∀ (k : ℕ) (b : Bool) (R : Rel), s.base R → ∃ R', s.base R' ∧
      ∀ x ws, (∀ w ∈ ws, s.Q x.length w) → (qpreP s R k b x ws ↔ R' x ws) := by
  intro k
  induction k with
  | zero => exact fun b R hR => ⟨R, hR, fun x ws _ => by simp⟩
  | succ k ih =>
      -- the existential side first; the universal side is its complement
      have htrue : ∀ R, s.base R → ∃ R', s.base R' ∧
          ∀ x ws, (∀ w ∈ ws, s.Q x.length w) → (qpreP s R (k + 1) true x ws ↔ R' x ws) := by
        intro R hR
        obtain ⟨R₁, hR₁, h₁⟩ := ih false R hR
        refine ⟨fun x ws => ExQ s R₁ x ws, habs R₁ hR₁, fun x ws hws => ?_⟩
        simp only [qpreP_succ_true, ExQ]
        refine exists_congr fun y => and_congr_right fun hy => h₁ x (ws ++ [y]) ?_
        intro w hw
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with hw | hw
        · exact hws w hw
        · exact hw ▸ hy
      intro b R hR
      cases b with
      | true => exact htrue R hR
      | false =>
          obtain ⟨R', hR', h⟩ := htrue (notRel R) (hcompl R hR)
          refine ⟨notRel R', hcompl R' hR', fun x ws hws => ?_⟩
          have hne : qpreP s (notRel R) (k + 1) true x ws ↔ ¬ qpreP s R (k + 1) false x ws :=
            qpreP_notRel R (k + 1) true x ws
          have key : R' x ws ↔ ¬ qpreP s R (k + 1) false x ws := (h x ws hws).symm.trans hne
          show qpreP s R (k + 1) false x ws ↔ ¬ R' x ws
          rw [key, not_not]

/-- **The hierarchy of a scale whose base class absorbs a quantifier collapses to its base
class.** -/
theorem collapseAt_zero_of_absorbEx (hcompl : ∀ R, s.base R → s.base (notRel R))
    (habs : AbsorbEx s) : CollapseAt s 0 := by
  intro j L hL
  obtain ⟨R, hR, hLR⟩ := (sigmaLevel_iff_qpreP j L).1 hL
  obtain ⟨R', hR', hiff⟩ := blockBase_of_absorbEx hcompl habs j true R hR
  exact (sigmaLevel_iff_qpreP 0 L).2 ⟨R', hR', fun x => (hLR x).trans (hiff x [] (by simp))⟩

/-- A base-class language is a `Σ₂` language: two dummy quantifiers are added. -/
theorem sigmaLevel_two_of_zero (hdrop : ∀ R, s.base R → s.base fun x ys => R x ys.dropLast)
    {L : Lang} (hL : SigmaLevel s 0 L) : SigmaLevel s 2 L := by
  obtain ⟨R, hR, hLR⟩ := (sigmaLevel_iff_qpreP 0 L).1 hL
  refine (sigmaLevel_iff_qpreP 2 L).2
    ⟨fun x ys => R x ys.dropLast.dropLast, hdrop _ (hdrop R hR), fun x => ?_⟩
  rw [hLR x]
  simp only [qpreP_zero, qpreP_succ_true, qpreP_succ_false]
  constructor
  · intro h
    exact ⟨[], s.Q_nil _, fun z _ => by simpa using h⟩
  · rintro ⟨y, -, h⟩
    simpa using h [] (s.Q_nil _)

/-- **The guard.**  If the base class of the scale is closed under complement and under ignoring
the last quantified string, and if it absorbs one existential quantifier, then the hierarchy
collapses to its second level — so the separation `¬ CollapseAt s 2` on which cells 3–5 of
Table 3 rest is *false* at such a scale.

The consequence for the interface: a source-side hardness family covering only the languages of
the base class of the scale cannot be re-read as one covering the `Σ₁` languages, on pain of
making the cells vacuous. -/
theorem collapseAt_two_of_absorbEx (hcompl : ∀ R, s.base R → s.base (notRel R))
    (hdrop : ∀ R, s.base R → s.base fun x ys => R x ys.dropLast) (habs : AbsorbEx s) :
    CollapseAt s 2 :=
  fun j L hL => sigmaLevel_two_of_zero hdrop (collapseAt_zero_of_absorbEx hcompl habs j L hL)

/-- The same, with the closure bundle of `Collapse.lean` in place of its two fields. -/
theorem collapseAt_two_of_absorbEx' (c : Closure s) (habs : AbsorbEx s) : CollapseAt s 2 :=
  collapseAt_two_of_absorbEx c.compl c.dropLast habs

end Hier

end HTN
