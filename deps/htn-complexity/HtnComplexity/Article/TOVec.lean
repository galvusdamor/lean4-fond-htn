import HtnComplexity.Article.TOSem
import HtnComplexity.PT.ExpTime
/-!
# States as Boolean vectors

The dynamic program of Thm. 4.2.1 ranges over all states, i.e. all subsets of the list `V` of
relevant facts (`HTN.Article.pfacts`).  A state is written as a Boolean vector over `V`
(`HTN.Article.vecOf`, read back by `HTN.Article.sv`); every vector of the right length is the
vector of its state (`HTN.Article.vecOf_sv`).  All vectors of length `n` are enumerated from a
padding of length at least `2 ^ n` (`HTN.Article.allVecs`, `HTN.Article.mem_allVecs`), in
polynomial time in the padding.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-- The facts of `V` marked in `v`. -/
def sv (V : List ℕ) (v : List Bool) : List ℕ :=
  (V.zip v).filterMap fun q => if q.2 then some q.1 else none

/-- The vector of a state. -/
def vecOf (V s : List ℕ) : List Bool := V.map fun f => decide (f ∈ s)

theorem sv_map (V : List ℕ) (g : ℕ → Bool) : sv V (V.map g) = V.filter g := by
  induction V with
  | nil => rfl
  | cons a V ih =>
    unfold sv at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons, List.filter_cons]
    cases g a <;> simp [ih]

theorem mem_sv_vecOf {V s : List ℕ} {f : ℕ} : f ∈ sv V (vecOf V s) ↔ f ∈ V ∧ f ∈ s := by
  rw [vecOf, sv_map]; simp [and_comm]

theorem length_vecOf (V s : List ℕ) : (vecOf V s).length = V.length := by simp [vecOf]

theorem sv_sub {V : List ℕ} {v : List Bool} {f : ℕ} (h : f ∈ sv V v) : f ∈ V := by
  unfold sv at h
  obtain ⟨q, hq, hf⟩ := List.mem_filterMap.1 h
  split_ifs at hf with hb
  · cases hf; exact List.of_mem_zip hq |>.1

/-- **Every vector over `V` is the vector of its state.** -/
theorem vecOf_sv : ∀ {V : List ℕ} {v : List Bool}, V.Nodup → v.length = V.length →
    vecOf V (sv V v) = v
  | [], [], _, _ => rfl
  | a :: V, b :: v, hnd, hl => by
    rw [List.nodup_cons] at hnd
    have hl' : v.length = V.length := by simpa using hl
    have ih := vecOf_sv hnd.2 hl'
    have hsv : sv (a :: V) (b :: v) = (if b then [a] else []) ++ sv V v := by
      unfold sv; cases b <;> simp
    have ha : a ∉ sv V v := fun h => hnd.1 (sv_sub h)
    unfold vecOf
    rw [hsv, List.map_cons]
    congr 1
    · cases b <;> simp [ha]
    · conv_rhs => rw [← ih]
      unfold vecOf
      refine List.map_congr_left fun f hf => ?_
      have hfa : f ≠ a := fun e => hnd.1 (e ▸ hf)
      cases b <;> simp [hfa]
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

/-! ### Enumerating the vectors -/

/-- The vector of length `|V|` of the binary digits of `i`. -/
def vecN (V : List ℕ) (i : ℕ) : List Bool := (List.range V.length).map fun j => (bitsOfNat i).getI j

/-- **All vectors of length `|V|`**, if the padding is at least `2 ^ |V|` long. -/
def allVecs (V : List ℕ) (pad : List Bool) : List (List Bool) :=
  ((List.range pad.length).filter fun i => decide ((bitsOfNat i).length ≤ V.length)).map (vecN V)

theorem getD_bitsOfNat_natOfBits : ∀ (v : List Bool) (j : ℕ),
    (bitsOfNat (natOfBits v)).getD j false = v.getD j false
  | [], j => by simp
  | b :: v, j => by
    have ih := getD_bitsOfNat_natOfBits v
    rw [natOfBits_cons]
    by_cases h0 : (if b then 1 else 0) + 2 * natOfBits v = 0
    · have hb : b = false := by cases b <;> simp_all
      have hm : natOfBits v = 0 := by omega
      subst hb
      rw [h0, bitsOfNat_zero]
      cases j with
      | zero => simp
      | succ j => rw [List.getD_cons_succ, ← ih j, hm, bitsOfNat_zero]; simp
    · obtain ⟨k, hk⟩ : ∃ k, (if b then 1 else 0) + 2 * natOfBits v = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_ne_zero h0).symm⟩
      rw [hk, bitsOfNat_succ, ← hk]
      have h1 : decide (((if b then 1 else 0) + 2 * natOfBits v) % 2 = 1) = b := by
        cases b <;> simp [Nat.add_mul_mod_self_left]
      have h2 : ((if b then 1 else 0) + 2 * natOfBits v) / 2 = natOfBits v := by
        cases b <;> simp <;> omega
      rw [h1, h2]
      cases j with
      | zero => simp
      | succ j => simp only [List.getD_cons_succ]; exact ih j

theorem natOfBits_lt : ∀ v : List Bool, natOfBits v < 2 ^ v.length
  | [] => by simp
  | b :: v => by
    have := natOfBits_lt v
    rw [natOfBits_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem length_vecN (V : List ℕ) (i : ℕ) : (vecN V i).length = V.length := by simp [vecN]

theorem vecN_natOfBits {V : List ℕ} {v : List Bool} (hv : v.length = V.length) :
    vecN V (natOfBits v) = v := by
  apply List.ext_getElem
  · simp [vecN, hv]
  · intro j h1 h2
    simp only [vecN, List.getElem_map, List.getElem_range]
    rw [← List.getD_default_eq_getI, show (default : Bool) = false from rfl,
      getD_bitsOfNat_natOfBits, List.getD_eq_getElem _ _ h2]

/-- **The enumeration contains all vectors of length `|V|`.** -/
theorem mem_allVecs {V : List ℕ} {pad : List Bool} (hpad : 2 ^ V.length ≤ pad.length)
    {v : List Bool} : v ∈ allVecs V pad ↔ v.length = V.length := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact length_vecN V i
  · intro hv
    have hlt := natOfBits_lt v
    rw [hv] at hlt
    refine List.mem_map.2 ⟨natOfBits v, List.mem_filter.2 ⟨List.mem_range.2 (by omega), ?_⟩,
      vecN_natOfBits hv⟩
    simpa using (length_bitsOfNat_le_iff _ _).2 hlt

theorem length_of_mem_allVecs {V : List ℕ} {pad : List Bool} {v : List Bool}
    (h : v ∈ allVecs V pad) : v.length = V.length := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
  exact length_vecN V i

theorem pt_allVecs {α : Type} [BEnc α] {V : α → List ℕ} {pad : α → List Bool} (hV : PT V)
    (hpad : PT pad) : PT fun a => allVecs (V a) (pad a) := by
  unfold allVecs vecN
  exact PT.map (g := fun a i => (List.range (V a).length).map fun j => (bitsOfNat i).getI j)
    (PT.filter (p := fun a (i : ℕ) => decide ((bitsOfNat i).length ≤ (V a).length))
      (PT.rangeLength hpad) (PT.le (PT.length (PT.bits.comp PT.snd)) (PT.length (hV.comp PT.fst))))
    (PT.map (g := fun (r : α × ℕ) (j : ℕ) => (bitsOfNat r.2).getI j)
      (PT.rangeLength (hV.comp PT.fst)) (PT.getI (PT.bits.comp (PT.snd.comp PT.fst)) PT.snd))

end Article

end HTN
