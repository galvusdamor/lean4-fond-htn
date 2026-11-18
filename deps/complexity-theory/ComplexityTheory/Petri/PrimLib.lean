import ComplexityTheory.Petri.IntPrimrec
/-!
# Generic primitive recursive list operations

Combinators missing from Mathlib that the certificate checker needs: parametric `filter`, `all`,
`any`, sums of integer / natural lists, `take`, `drop`, membership, `dedup`, `pow`, maximum.
-/

namespace HTN

namespace Petri

namespace PR

open Primrec

variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem list_filter {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).filter (p a) :=
  (listFilterMap hf ((Primrec.cond (hp.comp fst snd) (option_some.comp snd)
    (const none)).to₂)).of_eq fun a => by
    rw [← List.filterMap_eq_filter]
    congr 1
    funext b
    simp only [Option.guard]
    split <;> simp_all

theorem list_all {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) :=
  (list_foldr hf (const true) ((Primrec.and.comp (hp.comp fst (fst.comp snd))
    (snd.comp snd)).to₂)).of_eq fun a => by
    induction f a with
    | nil => rfl
    | cons x xs ih => simp [ih]

theorem list_any {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) :=
  (list_foldr hf (const false) ((Primrec.or.comp (hp.comp fst (fst.comp snd))
    (snd.comp snd)).to₂)).of_eq fun a => by
    induction f a with
    | nil => rfl
    | cons x xs ih => simp [ih]

theorem list_sumZ : Primrec fun l : List ℤ => l.sum :=
  (list_foldr Primrec.id (const 0) ((IntPR.add.comp (fst.comp snd)
    (snd.comp snd)).to₂)).of_eq fun l => by
    simp only [id]
    induction l with
    | nil => rfl
    | cons x xs ih => rw [List.foldr_cons, ih, List.sum_cons]

theorem list_sumN : Primrec fun l : List ℕ => l.sum :=
  (list_foldr Primrec.id (const 0) ((nat_add.comp (fst.comp snd)
    (snd.comp snd)).to₂)).of_eq fun l => by
    simp only [id]
    induction l with
    | nil => rfl
    | cons x xs ih => rw [List.foldr_cons, ih, List.sum_cons]

theorem list_maxN : Primrec fun l : List ℕ => l.foldr max 0 :=
  (list_foldr Primrec.id (const 0) ((nat_max.comp (fst.comp snd)
    (snd.comp snd)).to₂)).of_eq fun _ => rfl

omit [Primcodable β] in
theorem take_eq_filterMap (l : List β) : ∀ n, l.take n = (List.range n).filterMap (l[·]?)
  | 0 => by simp
  | n + 1 => by
    rw [List.take_add_one, take_eq_filterMap l n, List.range_succ, List.filterMap_append]
    congr 1

theorem list_take : Primrec₂ fun (l : List β) (n : ℕ) => l.take n :=
  (listFilterMap (list_range.comp snd) (list_getElem?.comp (fst.comp fst) snd).to₂).of_eq
    fun p => (take_eq_filterMap p.1 p.2).symm

omit [Primcodable β] in
theorem drop_eq_iterate (l : List β) : ∀ n, l.drop n = List.tail^[n] l
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', ← drop_eq_iterate l n, List.tail_drop]

theorem list_drop : Primrec₂ fun (l : List β) (n : ℕ) => l.drop n :=
  (nat_iterate snd fst (list_tail.comp snd).to₂).of_eq fun p => (drop_eq_iterate p.1 p.2).symm

theorem list_mem [DecidableEq β] : PrimrecRel fun (b : β) (l : List β) => b ∈ l :=
  (Primrec.eq.comp (list_any snd (Primrec.beq.comp snd (fst.comp fst)).to₂) (const true) :
    PrimrecPred fun q : β × List β => (q.2.any fun c => c == q.1) = true).of_eq fun q => by simp

omit [Primcodable β] in
theorem dedup_eq_foldr [DecidableEq β] (l : List β) :
    l.dedup = l.foldr (fun a r => if a ∈ r then r else a :: r) [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ← ih]
    by_cases h : a ∈ l
    · rw [List.dedup_cons_of_mem h, if_pos (List.mem_dedup.2 h)]
    · rw [List.dedup_cons_of_notMem h, if_neg (mt List.mem_dedup.1 h)]

theorem list_dedup [DecidableEq β] : Primrec fun l : List β => l.dedup :=
  (list_foldr Primrec.id (const []) (Primrec.ite
    (list_mem.comp (fst.comp snd) (snd.comp snd)) (snd.comp snd)
    (list_cons.comp (fst.comp snd) (snd.comp snd))).to₂).of_eq fun l => (dedup_eq_foldr l).symm

theorem nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem list_replicate : Primrec₂ fun (n : ℕ) (a : β) => List.replicate n a :=
  (list_map (list_range.comp fst) (snd.comp fst).to₂).of_eq fun p => by
    simp only [List.map_const', List.length_range]

end PR

end Petri

end HTN
