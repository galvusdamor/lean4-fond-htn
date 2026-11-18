import HtnComplexity.SpaceEnc.Complete
import HtnComplexity.Computable.RenderTR
import HtnComplexity.Space.NexpFamily
import Mathlib.Tactic.DeriveCountable

/-!
# The encoding as a pair of descriptions

The semantic problem `HTN.SpaceEnc.prob m n' ι N w` is written down as a domain description and
an instance description (`HTN.Syn.Rendering`):

* the facts are numbered so that `boot0` gets `0` and the input fact `inp i b` (`i < n`) gets the
  positional number `posFact (n - 1 - i) b`; hence the instance description of a word `w` of
  length `n` is `HTN.Space.hardInst w` (`HTN.SpaceEnc.instDesc_rend`), the instance map of the
  `NEXPTIME` family, whose polynomial-time computability and injectivity are already proved;
* the compound task `root` gets the number `0`;
* the domain description does not depend on the word, only on its length
  (`HTN.SpaceEnc.domDesc_rend_eq`);
* it is tail recursive (`HTN.SpaceEnc.isTailRec_domDesc_rend`) by a rank function on the compound
  tasks: only the loops `Loop p → [Block p, Loop p]` and `Drain → [drn, Drain]` keep the rank, in
  the last cell of a single row;
* `HTN.SpaceEnc.solvable_rend_iff` — the described problem is solvable iff the machine accepts in
  space `2 ^ m`.
-/

deriving instance Countable for TM.Move
deriving instance Countable for HTN.SpaceEnc.Fct
deriving instance Countable for HTN.SpaceEnc.Act
deriving instance Countable for HTN.SpaceEnc.Cmp

namespace HTN

namespace SpaceEnc

open TM Syn TaskNetwork

variable {Q Γ : Type}

/-! ### The numberings -/

section Num

variable [Fintype Q] [Fintype Γ]

/-- An injective numbering of the facts. -/
noncomputable def cF : Fct Q Γ → ℕ := @Encodable.encode _ (Encodable.ofCountable _)

/-- An injective numbering of the actions. -/
noncomputable def cA : Act Q Γ → ℕ := @Encodable.encode _ (Encodable.ofCountable _)

/-- An injective numbering of the compound tasks. -/
noncomputable def cC : Cmp → ℕ := @Encodable.encode _ (Encodable.ofCountable _)

theorem cF_injective : Function.Injective (cF : Fct Q Γ → ℕ) :=
  @Encodable.encode_injective _ (Encodable.ofCountable _)

theorem cA_injective : Function.Injective (cA : Act Q Γ → ℕ) :=
  @Encodable.encode_injective _ (Encodable.ofCountable _)

theorem cC_injective : Function.Injective cC :=
  @Encodable.encode_injective _ (Encodable.ofCountable _)

/-- **The numbering of the facts** for the inputs of length `n`: `boot0 ↦ 0`, the input fact of
position `i < n` the positional fact of `HTN.Syn.posFacts`, everything else above `2n + 1`. -/
noncomputable def eF (n : ℕ) : Fct Q Γ → ℕ
  | .boot0 => 0
  | .inp i b => if i < n then posFact (n - 1 - i) b else 2 * n + 2 + cF (Fct.inp i b : Fct Q Γ)
  | f => 2 * n + 2 + cF f

theorem eF_cases (n : ℕ) (f : Fct Q Γ) :
    (f = .boot0 ∧ eF n f = 0) ∨ (∃ i b, i < n ∧ f = .inp i b ∧ eF n f = posFact (n - 1 - i) b) ∨
      eF n f = 2 * n + 2 + cF f := by
  cases f with
  | boot0 => exact Or.inl ⟨rfl, rfl⟩
  | inp i b =>
    by_cases hi : i < n
    · exact Or.inr (Or.inl ⟨i, b, hi, rfl, by simp [eF, hi]⟩)
    · exact Or.inr (Or.inr (by simp [eF, hi]))
  | _ => exact Or.inr (Or.inr rfl)

theorem posFact_bounds {n i : ℕ} (hi : i < n) (b : Bool) :
    2 ≤ posFact (n - 1 - i) b ∧ posFact (n - 1 - i) b < 2 * n + 2 := by
  unfold posFact; cases b <;> simp <;> omega

theorem eF_injective (n : ℕ) : Function.Injective (eF n : Fct Q Γ → ℕ) := by
  intro x y h
  rcases eF_cases n x with ⟨rfl, hx⟩ | ⟨i, b, hi, rfl, hx⟩ | hx <;>
    rcases eF_cases n y with ⟨rfl, hy⟩ | ⟨j, c, hj, rfl, hy⟩ | hy
  · rfl
  · have := posFact_bounds hj c; omega
  · omega
  · have := posFact_bounds hi b; omega
  · rw [hx, hy] at h
    unfold posFact at h
    have hij : i = j := by cases b <;> cases c <;> simp at h <;> omega
    subst hij
    have hbc : b = c := by cases b <;> cases c <;> simp at h ⊢
    rw [hbc]
  · have := posFact_bounds hi b; omega
  · omega
  · have := posFact_bounds hj c; omega
  · exact cF_injective (by omega)

/-- **The numbering of the compound tasks**: `root ↦ 0`. -/
noncomputable def eC (c : Cmp) : ℕ := if c = .root then 0 else cC c + 1

theorem eC_injective : Function.Injective eC := by
  intro x y h
  unfold eC at h
  by_cases hx : x = .root <;> by_cases hy : y = .root
  · rw [hx, hy]
  · rw [if_pos hx, if_neg hy] at h; omega
  · rw [if_neg hx, if_pos hy] at h; omega
  · rw [if_neg hx, if_neg hy] at h
    exact cC_injective (by omega)

end Num

/-! ### The rendering -/

section Rend

variable [Fintype Q] [Fintype Γ] (m n' : ℕ) (ι : Bool → Γ) (N : NTM Q Γ)

/-- The actions occurring in the method bodies. -/
noncomputable def actsL : List (Act Q Γ) :=
  (bodies m n' N).flatMap fun b => b.2.flatten.filterMap fun x => x.getLeft?

theorem mem_flatten_of_cell {α : Type} {ls : List (List α)} {i j : ℕ} {d : α}
    (hi : i < ls.length) (hj : j < (ls.getD i []).length) : (ls.getD i []).getD j d ∈ ls.flatten := by
  rw [List.mem_flatten]
  refine ⟨ls.getD i [], ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-- **The rendering of the encoding** for the inputs of length `n`. -/
noncomputable def rend (n : ℕ) (w : List Bool) : Rendering (prob m n' ι N w) where
  eF := eF n
  eA := cA
  eC := eC
  eF_inj := eF_injective n
  eA_inj := cA_injective
  eC_inj := eC_injective
  acts := actsL m n' N
  precL := precL m n'
  addL := addL m ι N
  delL := delL m
  bodies := (bodies m n' N).map fun b => (b.1, ⟨b.2, 0⟩)
  tnIshape := ⟨[[Sum.inr Cmp.root]], 0⟩
  initL := Fct.boot0 :: inpL w
  goalL := []
  used_mem := by
    rintro o (⟨t, ht, hα⟩ | ⟨mt, hmt, t, ht, hα⟩)
    · have ht' := mem_grid_T.1 ht
      simp only [List.length_singleton, Nat.lt_one_iff] at ht'
      obtain ⟨h1, h2⟩ := ht'
      have : t = (0, 0) := Prod.ext h1 (by simpa [h1] using h2)
      subst this
      exact absurd hα (by simp [prob, TaskNetwork.grid])
    · obtain ⟨b, hb, rfl⟩ := hmt
      have ht' := mem_grid_T.1 ht
      have hmem := mem_flatten_of_cell (d := (Sum.inl default : Act Q Γ ⊕ Cmp)) ht'.1 ht'.2
      have hα' : (b.2.getD t.1 []).getD t.2 (Sum.inl default) = Sum.inl o := hα
      rw [hα'] at hmem
      simp only [actsL, List.mem_flatMap, List.mem_filterMap]
      exact ⟨b, hb, Sum.inl o, hmem, rfl⟩
  precL_eq := fun _ _ => rfl
  addL_eq := fun _ _ => rfl
  delL_eq := fun _ _ => rfl
  init_eq := rfl
  goal_eq := by simp [prob]
  tnI_wf := TaskNetwork.grid_wf
  tnI_iso := by rw [prob, Shape.net_zero]
  bodies_sub := fun p hp => by
    simp only [List.mem_map] at hp
    obtain ⟨b, hb, rfl⟩ := hp
    exact ⟨⟨b.1, TaskNetwork.grid b.2⟩, ⟨b, hb, rfl⟩, rfl, by
      rw [Shape.net_zero]⟩
  bodies_all := fun mt hm => by
    obtain ⟨b, hb, rfl⟩ := hm.1
    exact ⟨(b.1, ⟨b.2, 0⟩), List.mem_map.2 ⟨b, hb, rfl⟩, rfl, by
      rw [Shape.net_zero]⟩

/-- The domain description does not depend on the word. -/
theorem domDesc_rend_eq (n : ℕ) (w w' : List Bool) :
    (rend m n' ι N n w).domDesc = (rend m n' ι N n w').domDesc := rfl

/-- **The instance description of a word is the instance of the `NEXPTIME` family.** -/
theorem instDesc_rend (w : List Bool) : (rend m n' ι N w.length w).instDesc = Space.hardInst w := by
  unfold Space.hardInst guardInst Rendering.instDesc
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · show eF (Q := Q) (Γ := Γ) w.length Fct.boot0 :: (inpL w).map (eF w.length) = 0 :: posFacts w
    rw [Space.posFacts_eq_range]
    simp only [inpL, List.map_map]
    refine congrArg _ (List.map_congr_left fun i hi => ?_)
    rw [List.mem_range] at hi
    simp [eF, hi]
  · show Shape.desc ⟨[[Sum.inr Cmp.root]], 0⟩ cA eC = _
    have : eC Cmp.root = 0 := by simp [eC]
    show (([0], [], [(0, true, eC Cmp.root)]) : TnDesc) = _
    rw [this]

variable [DecidableEq Q] [DecidableEq Γ]

/-- **The described problem is solvable iff the machine accepts in space `2 ^ m`.** -/
theorem solvable_rend_iff {w : List Bool} (hn' : n' = w.length) (n : ℕ) :
    Solvable (rend m n' ι N n w).domDesc (rend m n' ι N n w).instDesc ↔
      N.AcceptsInSpace (w.map ι) (2 ^ m) :=
  (rend m n' ι N n w).solvable_iff.trans (solvable_iff_accepts hn')

end Rend

end SpaceEnc

end HTN
