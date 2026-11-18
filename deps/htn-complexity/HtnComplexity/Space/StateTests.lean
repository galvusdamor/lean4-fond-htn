import HtnComplexity.Space.TblSolver
import HtnComplexity.Complexity.SerAny
/-!
# The three tests on encoded states

A configuration of the target-side machine is a state of the transition system of
`HtnComplexity/Space/StripsSystem.lean`, written as the serialised list of the binary
numerals of its facts (`HTN.Space.encState`).  The transition relation

    StepTbl tbl s s' :
      some row is applicable in `s`, and `s'` carries exactly the facts the row leaves behind

is, on encoded states, a conjunction of three tests, and this file provides them, each of them a
predicate of Cobham's class by the quantifier of
`HtnComplexity/Complexity/SerAny.lean`:

* `HTN.Space.subEntB y z` — every fact of the state that starts `y` is a fact of the state that
  starts `z`.  This is "the precondition of the row holds", and also "the goal is reached";
* `HTN.Space.keepB y d c` — every fact of the state that starts `y` is deleted by `d` or survives
  into `c`.  This is the "nothing is lost" half of the postcondition;
* `HTN.Space.postB y a c d` — every fact of the state that starts `y` is added by `a`, or was
  there in `c` and is not deleted by `d`.  This is the "nothing is invented" half.

Each comes with its reading on serialised states (`HTN.Space.subEntB_encState` and friends), in
which the strings carry arbitrary junk after the state — which is what lets the machine address
the three lists of a row, and the initial state and the goal of its input, by a suffix rather
than by cutting them out.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### The tests -/

/-- Every entry of the serialised list that starts `y` occurs in the one that starts `z`. -/
def subEntB (y z : List Bool) : Bool :=
  allEntB (fun args => occB (args.getD 1 []) (args.getD 0 [])) y z [] []

/-- Every entry of the serialised list that starts `y` occurs in the one that starts `d` or in
the one that starts `c`. -/
def keepB (y d c : List Bool) : Bool :=
  allEntB (fun args => occB (args.getD 1 []) (args.getD 0 []) ||
    occB (args.getD 2 []) (args.getD 0 [])) y d c []

/-- Every entry of the serialised list that starts `y` occurs in the one that starts `a`, or
occurs in the one that starts `c` and not in the one that starts `d`. -/
def postB (y a c d : List Bool) : Bool :=
  allEntB (fun args => occB (args.getD 1 []) (args.getD 0 []) ||
    (occB (args.getD 2 []) (args.getD 0 []) && !occB (args.getD 3 []) (args.getD 0 []))) y a c d

/-! ### Correctness on serialised lists -/

theorem subEntB_iff (l m : List (List Bool)) (z₁ z₂ : List Bool) :
    subEntB (blist l ++ z₁) (blist m ++ z₂) = true ↔ ∀ w ∈ l, w ∈ m := by
  rw [subEntB, allEntB_iff]
  exact forall₂_congr fun w _ => by
    simpa using occB_iff m z₂ w

theorem keepB_iff (l m k : List (List Bool)) (z₁ z₂ z₃ : List Bool) :
    keepB (blist l ++ z₁) (blist m ++ z₂) (blist k ++ z₃) = true ↔
      ∀ w ∈ l, w ∈ m ∨ w ∈ k := by
  rw [keepB, allEntB_iff]
  refine forall₂_congr fun w _ => ?_
  simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.or_eq_true]
  rw [occB_iff m z₂ w, occB_iff k z₃ w]

theorem postB_iff (l a c d : List (List Bool)) (z₁ z₂ z₃ z₄ : List Bool) :
    postB (blist l ++ z₁) (blist a ++ z₂) (blist c ++ z₃) (blist d ++ z₄) = true ↔
      ∀ w ∈ l, w ∈ a ∨ (w ∈ c ∧ w ∉ d) := by
  rw [postB, allEntB_iff]
  refine forall₂_congr fun w _ => ?_
  simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true]
  rw [occB_iff a z₂ w, occB_iff c z₃ w,
    ← Bool.not_eq_true (occB (blist d ++ z₄) (true :: bstr w)), occB_iff d z₄ w]

/-! ### Correctness on encoded states -/

theorem mem_map_bitsOfNat {s : List ℕ} {w : List Bool} :
    w ∈ s.map bitsOfNat ↔ ∃ f ∈ s, bitsOfNat f = w := by
  simp [List.mem_map]

theorem mem_map_bitsOfNat_iff {s : List ℕ} {f : ℕ} :
    bitsOfNat f ∈ s.map bitsOfNat ↔ f ∈ s := by
  constructor
  · rintro h
    obtain ⟨g, hg, hge⟩ := List.mem_map.1 h
    rwa [bitsOfNat_injective hge] at hg
  · exact fun h => List.mem_map_of_mem h

theorem subEntB_encState (s t : List ℕ) (z₁ z₂ : List Bool) :
    subEntB (encState s ++ z₁) (encState t ++ z₂) = true ↔ ∀ f ∈ s, f ∈ t := by
  rw [encState, encState, subEntB_iff]
  constructor
  · intro h f hf
    exact mem_map_bitsOfNat_iff.1 (h _ (List.mem_map_of_mem hf))
  · rintro h w hw
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hw
    exact List.mem_map_of_mem (h f hf)

theorem keepB_encState (s d c : List ℕ) (z₁ z₂ z₃ : List Bool) :
    keepB (encState s ++ z₁) (encState d ++ z₂) (encState c ++ z₃) = true ↔
      ∀ f ∈ s, f ∈ d ∨ f ∈ c := by
  rw [encState, encState, encState, keepB_iff]
  constructor
  · intro h f hf
    rcases h _ (List.mem_map_of_mem hf) with hd | hc
    · exact Or.inl (mem_map_bitsOfNat_iff.1 hd)
    · exact Or.inr (mem_map_bitsOfNat_iff.1 hc)
  · rintro h w hw
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hw
    rcases h f hf with hd | hc
    · exact Or.inl (List.mem_map_of_mem hd)
    · exact Or.inr (List.mem_map_of_mem hc)

theorem postB_encState (s a c d : List ℕ) (z₁ z₂ z₃ z₄ : List Bool) :
    postB (encState s ++ z₁) (encState a ++ z₂) (encState c ++ z₃) (encState d ++ z₄) = true ↔
      ∀ f ∈ s, f ∈ a ∨ (f ∈ c ∧ f ∉ d) := by
  rw [encState, encState, encState, encState, postB_iff]
  constructor
  · intro h f hf
    rcases h _ (List.mem_map_of_mem hf) with ha | ⟨hc, hd⟩
    · exact Or.inl (mem_map_bitsOfNat_iff.1 ha)
    · exact Or.inr ⟨mem_map_bitsOfNat_iff.1 hc, fun hmem => hd (List.mem_map_of_mem hmem)⟩
  · rintro h w hw
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hw
    rcases h f hf with ha | ⟨hc, hd⟩
    · exact Or.inl (List.mem_map_of_mem ha)
    · exact Or.inr ⟨List.mem_map_of_mem hc, fun hmem => hd (mem_map_bitsOfNat_iff.1 hmem)⟩

/-! ### The three tests are predicates of Cobham's class -/

theorem cobhamB_subEntB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => subEntB (a args) (b args) :=
  (cobhamB_allEntB (cobhamB_occB (Cobham.proj 1) (Cobham.proj 0)) ha hb
    Cobham.empty Cobham.empty).of_eq fun args => by simp [subEntB, proj]

theorem cobhamB_keepB {a b c : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => keepB (a args) (b args) (c args) :=
  (cobhamB_allEntB
    ((cobhamB_occB (Cobham.proj 1) (Cobham.proj 0)).or
      (cobhamB_occB (Cobham.proj 2) (Cobham.proj 0))) ha hb hc Cobham.empty).of_eq
    fun args => by simp [keepB, proj]

theorem cobhamB_postB {a b c d : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c)
    (hd : Cobham d) : CobhamB fun args => postB (a args) (b args) (c args) (d args) :=
  (cobhamB_allEntB
    ((cobhamB_occB (Cobham.proj 1) (Cobham.proj 0)).or
      ((cobhamB_occB (Cobham.proj 2) (Cobham.proj 0)).and
        (cobhamB_occB (Cobham.proj 3) (Cobham.proj 0)).not)) ha hb hc hd).of_eq
    fun args => by simp [postB, proj]

end Space

end HTN
