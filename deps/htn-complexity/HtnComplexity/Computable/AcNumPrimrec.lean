import ComplexityTheory.Computable.PrimrecPow
import HtnPlanning.Computable.Syntax
/-!
# The numbering of the compiled signature is primitive recursive

`HtnComplexity/Computable/AcNum.lean` writes the facts, actions and compound tasks of the
compiled acyclic domain as numbers — `fPos v i = 6·(5v+i)+3`, `tSELn n i = 13·(5n+i)+1`, and so
on.  This file records that each of those functions is primitive recursive, and adds the two
general list utilities the translation needs: a primitive-recursive duplicate removal
(`HTN.Syn.Ac.dedupN`, equal to `List.dedup`) and a primitive-recursive association-list lookup
(`HTN.Syn.Ac.lookupN`, equal to `List.lookup`).
-/

namespace HTN

namespace Syn

namespace Ac

open Primrec


/-- Iterating a primitive-recursive step is primitive recursive. -/
theorem primrec_iterate {σ : Type} [Primcodable σ] {step : σ → σ} (hs : Primrec step) :
    Primrec₂ (fun (p : σ) (n : ℕ) => step^[n] p) := by
  have h := Primrec.nat_rec (f := fun p : σ => p) (g := fun (_ : σ) (q : ℕ × σ) => step q.2)
    Primrec.id (hs.comp (Primrec.snd.comp Primrec.snd))
  refine Primrec₂.mk ((h.comp Primrec.fst Primrec.snd).of_eq fun x => ?_)
  obtain ⟨p, n⟩ := x
  induction n with
  | zero => rfl
  | succ k ih =>
      show step (Nat.rec p (fun _ IH => step IH) k) = _
      rw [Function.iterate_succ_apply']
      simp only at ih ⊢
      rw [ih]

/-! ### Duplicate removal -/

/-- A primitive-recursive duplicate removal. -/
def dedupN (l : List ℕ) : List ℕ := l.foldr (fun a r => if memB r a then r else a :: r) []

theorem dedupN_eq (l : List ℕ) : dedupN l = l.dedup := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show (if memB (dedupN t) a then dedupN t else a :: dedupN t) = (a :: t).dedup
    rw [ih]
    by_cases h : a ∈ t
    · rw [if_pos (memB_iff.2 (List.mem_dedup.2 h)), List.dedup_cons_of_mem h]
    · rw [show memB t.dedup a = false by
        simp only [Bool.eq_false_iff, ne_eq]
        intro hc
        exact h (List.mem_dedup.1 (memB_iff.1 hc)), if_neg (by simp),
        List.dedup_cons_of_notMem h]

theorem primrec_dedupN : Primrec dedupN := by
  have h : Primrec₂ fun (_ : List ℕ) (p : ℕ × List ℕ) =>
      if memB p.2 p.1 then p.2 else p.1 :: p.2 := by
    refine Primrec.ite (PrimrecRel.comp Primrec.eq
      (primrec_memB.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
      (Primrec.const true)) (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr Primrec.id (Primrec.const ([] : List ℕ)) h).of_eq fun _ => rfl

/-- **Duplicate removal is primitive recursive.** -/
theorem primrec_dedup : Primrec (fun l : List ℕ => l.dedup) :=
  primrec_dedupN.of_eq dedupN_eq

/-! ### Association-list lookup -/

/-- Association-list lookup, as a fold. -/
def lookupN {β : Type} (l : List (ℕ × β)) (k : ℕ) : Option β :=
  l.foldr (fun p r => if p.1 = k then some p.2 else r) none

theorem lookupN_eq {β : Type} (l : List (ℕ × β)) (k : ℕ) : lookupN l k = l.lookup k := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    show (if p.1 = k then some p.2 else lookupN ps k) = _
    rw [ih, List.lookup_cons]
    by_cases h : k = p.1
    · subst h; simp
    · rw [if_neg (fun hc => h hc.symm), show (k == p.1) = false by simp [h]]

theorem primrec_lookupN {β : Type} [Primcodable β] : Primrec₂ (lookupN (β := β)) := by
  have h : Primrec₂ fun (x : List (ℕ × β) × ℕ) (p : (ℕ × β) × Option β) =>
      if p.1.1 = x.2 then some p.1.2 else p.2 := by
    refine Primrec.ite (PrimrecRel.comp Primrec.eq
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.fst))
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  have hf := Primrec.list_foldr (f := fun x : List (ℕ × β) × ℕ => x.1)
    (g := fun _ : List (ℕ × β) × ℕ => (none : Option β)) Primrec.fst (Primrec.const none) h
  exact Primrec₂.mk (hf.of_eq fun _ => rfl)

/-- **Association-list lookup is primitive recursive.** -/
theorem primrec_lookup {β : Type} [Primcodable β] :
    Primrec₂ (fun (l : List (ℕ × β)) (k : ℕ) => l.lookup k) := by
  have h : Primrec fun x : List (ℕ × β) × ℕ => lookupN x.1 x.2 := primrec_lookupN
  exact Primrec₂.mk (h.of_eq fun x => lookupN_eq x.1 x.2)

end Ac

end Syn

end HTN
