import ComplexityTheory.HDDecide.Petri
/-!
# Petri net reachability and coverability are recursively enumerable

* `HTN.Petri.rePred_exists` — a predicate `∃ w, q a w` with `q` primitive recursive is
  recursively enumerable (the generic "search for a witness" principle);
* `HTN.Petri.fireL_iff` — firing a transition, decided on lists;
* `HTN.Petri.reach_re` — **Petri net reachability is recursively enumerable**;
* `HTN.Petri.cover_re` — **Petri net coverability is recursively enumerable**.

The two semi-decision procedures guess the sequence of intermediate markings.
-/

namespace HTN

namespace Petri

open Primrec

/-! ### Primitive recursive predicates -/

/-- A primitive recursive predicate, decided with the classical instance. -/
theorem PrimrecPred.classical' {α : Type*} [Primcodable α] {p : α → Prop} (h : PrimrecPred p) :
    Primrec fun a => @decide (p a) (Classical.propDecidable _) := by
  obtain ⟨_, h⟩ := h
  exact h.of_eq fun a => by congr 1

theorem primrecPred_forall_mem {α β : Type*} [Primcodable α] [Primcodable β] {f : α → List β}
    {q : α → β → Prop} (hf : Primrec f) (hq : PrimrecPred fun p : α × β => q p.1 p.2) :
    PrimrecPred fun a => ∀ b ∈ f a, q a b := by
  classical
  have hq' := PrimrecPred.classical' hq
  have h : Primrec₂ fun (a : α) (z : β × Bool) => decide (q a z.1) && z.2 :=
    Primrec₂.mk (Primrec.and.comp (hq'.comp (Primrec.pair Primrec.fst
      (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))
  refine ⟨inferInstance, (Primrec.list_foldr hf (Primrec.const true) h).of_eq fun a => ?_⟩
  dsimp only
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  induction f a with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem primrecPred_exists_mem {α β : Type*} [Primcodable α] [Primcodable β] {f : α → List β}
    {q : α → β → Prop} (hf : Primrec f) (hq : PrimrecPred fun p : α × β => q p.1 p.2) :
    PrimrecPred fun a => ∃ b ∈ f a, q a b := by
  classical
  have hq' := PrimrecPred.classical' hq
  have h : Primrec₂ fun (a : α) (z : β × Bool) => decide (q a z.1) || z.2 :=
    Primrec₂.mk (Primrec.or.comp (hq'.comp (Primrec.pair Primrec.fst
      (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))
  refine ⟨inferInstance, (Primrec.list_foldr hf (Primrec.const false) h).of_eq fun a => ?_⟩
  dsimp only
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  induction f a with
  | nil => simp
  | cons x xs ih => simp [ih]

/-! ### Searching for a witness -/

/-- **A predicate with a primitive recursive witness relation is r.e.** -/
theorem rePred_exists {α β : Type*} [Primcodable α] [Primcodable β] {q : α → β → Prop}
    (hq : PrimrecPred fun p : α × β => q p.1 p.2) : REPred fun a => ∃ b, q a b := by
  classical
  have hq' := PrimrecPred.classical' hq
  let f : α → ℕ → Option β := fun a n =>
    (Encodable.decode (α := β) n).bind fun b => if q a b then some b else none
  have hf : Computable₂ f := by
    have h1 : Primrec₂ fun (a : α) (n : ℕ) => Encodable.decode (α := β) n :=
      (Primrec.decode.comp Primrec.snd).to₂
    have h2 : Primrec₂ fun (p : α × ℕ) (b : β) => if q p.1 b then some b else none := by
      refine Primrec₂.mk (Primrec.ite ?_ (Primrec.option_some.comp Primrec.snd)
        (Primrec.const none))
      exact ⟨inferInstance, (hq'.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        Primrec.snd)).of_eq fun _ => rfl⟩
    exact (Primrec.option_bind h1 h2).to_comp.to₂
  refine (Partrec.rfindOpt hf).dom_re.of_eq fun a => ?_
  rw [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨n, b, hb⟩
    simp only [f, Option.mem_def, Option.bind_eq_some_iff] at hb
    obtain ⟨b', -, hb'⟩ := hb
    split_ifs at hb' with h
    · cases hb'; exact ⟨b, h⟩
  · rintro ⟨b, hb⟩
    refine ⟨Encodable.encode b, b, ?_⟩
    simp [f, Encodable.encodek, hb]

/-! ### Multiset arithmetic on lists -/

/-- The number of occurrences, as a fold (primitive recursive). -/
def cnt (p : ℕ) (l : List ℕ) : ℕ := l.foldr (fun x n => if x = p then n + 1 else n) 0

theorem cnt_eq (p : ℕ) (l : List ℕ) : cnt p l = Multiset.count p (l : Multiset ℕ) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [cnt, List.foldr_cons] at ih ⊢
    rw [ih, ← Multiset.cons_coe, Multiset.count_cons]
    by_cases h : x = p
    · subst h; simp
    · simp [h, Ne.symm h]

theorem primrec_cnt : Primrec₂ cnt := by
  have h : Primrec₂ fun (w : ℕ × List ℕ) (z : ℕ × ℕ) => if z.1 = w.1 then z.2 + 1 else z.2 :=
    Primrec₂.mk (Primrec.ite (PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)) (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
  exact Primrec₂.mk ((Primrec.list_foldr Primrec.snd (Primrec.const 0) h).of_eq fun w => rfl)

/-- `a ≤ b` as multisets, on lists. -/
def LeL (a b : List ℕ) : Prop := ∀ p ∈ a, cnt p a ≤ cnt p b

theorem leL_iff {a b : List ℕ} : LeL a b ↔ (a : Multiset ℕ) ≤ (b : Multiset ℕ) := by
  rw [Multiset.le_iff_count]
  constructor
  · intro h p
    by_cases hp : p ∈ a
    · simpa [cnt_eq] using h p hp
    · rw [Multiset.count_eq_zero_of_notMem (by simpa using hp)]; exact Nat.zero_le _
  · intro h p _
    simpa [cnt_eq] using h p

theorem primrec_leL : PrimrecPred fun w : List ℕ × List ℕ => LeL w.1 w.2 :=
  primrecPred_forall_mem Primrec.fst
    (PrimrecRel.comp Primrec.nat_le (primrec_cnt.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
      (primrec_cnt.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))

/-- `b = a - pre + post` as multisets, on lists. -/
def EffL (a pre post b : List ℕ) : Prop :=
  ∀ p ∈ a ++ pre ++ post ++ b, cnt p b + cnt p pre = cnt p a + cnt p post

theorem effL_iff {a pre post b : List ℕ} (hle : (pre : Multiset ℕ) ≤ (a : Multiset ℕ)) :
    EffL a pre post b ↔
      (b : Multiset ℕ) = (a : Multiset ℕ) - (pre : Multiset ℕ) + (post : Multiset ℕ) := by
  rw [Multiset.ext]
  have hle' := Multiset.le_iff_count.1 hle
  constructor
  · intro h p
    rw [Multiset.count_add, Multiset.count_sub]
    by_cases hp : p ∈ a ++ pre ++ post ++ b
    · have := h p hp
      simp only [cnt_eq] at this
      have := hle' p
      omega
    · simp only [List.mem_append, not_or] at hp
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
      simp [Multiset.count_eq_zero_of_notMem, h1, h2, h3, h4]
  · intro h p _
    have := h p
    rw [Multiset.count_add, Multiset.count_sub] at this
    have := hle' p
    simp only [cnt_eq]
    omega

theorem primrec_effL :
    PrimrecPred fun w : (List ℕ × List ℕ) × (List ℕ × List ℕ) => EffL w.1.1 w.1.2 w.2.1 w.2.2 := by
  have hl : Primrec fun w : (List ℕ × List ℕ) × (List ℕ × List ℕ) =>
      w.1.1 ++ w.1.2 ++ w.2.1 ++ w.2.2 :=
    Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  refine primrecPred_forall_mem hl ?_
  let c : (List ℕ × List ℕ) × (List ℕ × List ℕ) → List ℕ := fun w => w.1.1
  have hc : ∀ {g : (List ℕ × List ℕ) × (List ℕ × List ℕ) → List ℕ}, Primrec g →
      Primrec fun z : ((List ℕ × List ℕ) × (List ℕ × List ℕ)) × ℕ => cnt z.2 (g z.1) :=
    fun hg => primrec_cnt.comp Primrec.snd (hg.comp Primrec.fst)
  exact PrimrecRel.comp Primrec.eq
    (Primrec.nat_add.comp (hc (Primrec.snd.comp Primrec.snd)) (hc (Primrec.snd.comp Primrec.fst)))
    (Primrec.nat_add.comp (hc (Primrec.fst.comp Primrec.fst)) (hc (Primrec.fst.comp Primrec.snd)))

/-! ### Firing, on lists -/

/-- **Firing a transition, decided on lists.** -/
def FireL (N : List (Trans ℕ)) (a b : List ℕ) : Prop :=
  ∃ t ∈ N, LeL t.1 a ∧ EffL a t.1 t.2 b

theorem fireL_iff {N : List (Trans ℕ)} {a b : List ℕ} :
    FireL N a b ↔ Fire N (a : Multiset ℕ) (b : Multiset ℕ) := by
  constructor
  · rintro ⟨t, ht, hle, heff⟩
    have hle' := leL_iff.1 hle
    exact ⟨t, ht, hle', (effL_iff hle').1 heff⟩
  · rintro ⟨t, ht, hle, heff⟩
    exact ⟨t, ht, leL_iff.2 hle, (effL_iff hle).2 heff⟩

theorem primrec_fireL :
    PrimrecPred fun w : List (Trans ℕ) × List ℕ × List ℕ => FireL w.1 w.2.1 w.2.2 := by
  refine primrecPred_exists_mem Primrec.fst ?_
  refine PrimrecPred.and ?_ ?_
  · exact primrec_leL.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  · exact primrec_effL.comp (Primrec.pair (Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.snd.comp (Primrec.snd.comp
        Primrec.fst))))

/-! ### Runs, on lists -/

/-- A sequence of markings `a = m₀, m₁, …, mₖ = b` (the witness lists `m₁ … mₖ`), each obtained
from the previous one by firing. -/
def RunL (N : List (Trans ℕ)) : List ℕ → List (List ℕ) → List ℕ → Prop
  | a, [], b => (a : Multiset ℕ) = (b : Multiset ℕ)
  | a, m :: ms, b => FireL N a m ∧ RunL N m ms b

theorem reach_iff_exists_runL {N : List (Trans ℕ)} {a b : List ℕ} :
    Reach N (a : Multiset ℕ) (b : Multiset ℕ) ↔ ∃ ms, RunL N a ms b := by
  constructor
  · intro h
    suffices key : ∀ x y : Multiset ℕ, Reach N x y → ∀ a : List ℕ, (a : Multiset ℕ) = x →
        (b : Multiset ℕ) = y → ∃ ms, RunL N a ms b from key _ _ h a rfl rfl
    intro x y hxy
    induction hxy using Relation.ReflTransGen.head_induction_on with
    | refl => intro a ha hb; exact ⟨[], by simp only [RunL]; rw [ha, hb]⟩
    | @head x' z hstep _ ih =>
      intro a ha hb
      obtain ⟨ms, hms⟩ := ih z.toList (Multiset.coe_toList z) hb
      refine ⟨z.toList :: ms, ?_, hms⟩
      rw [fireL_iff, ha, Multiset.coe_toList]
      exact hstep
  · rintro ⟨ms, hms⟩
    induction ms generalizing a with
    | nil => simp only [RunL] at hms; rw [hms]; exact Relation.ReflTransGen.refl
    | cons m ms ih =>
      obtain ⟨h1, h2⟩ := hms
      exact Relation.ReflTransGen.head (fireL_iff.1 h1) (ih h2)

/-- A run, as an index-wise check (primitive recursive). -/
def RunI (N : List (Trans ℕ)) (a : List ℕ) (ms : List (List ℕ)) (b : List ℕ) : Prop :=
  (∀ i ∈ List.range ms.length, FireL N ((a :: ms).getD i []) (ms.getD i [])) ∧
    (LeL ((a :: ms).getD ms.length []) b ∧ LeL b ((a :: ms).getD ms.length []))

theorem runL_iff_runI {N : List (Trans ℕ)} {a : List ℕ} {ms : List (List ℕ)} {b : List ℕ} :
    RunL N a ms b ↔ RunI N a ms b := by
  induction ms generalizing a with
  | nil =>
    simp only [RunL, RunI, List.length_nil, List.range_zero, List.not_mem_nil, false_imp_iff,
      imp_true_iff, true_and, List.getD_cons_zero, leL_iff]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  | cons m ms ih =>
    simp only [RunL, RunI] at ih ⊢
    rw [ih]
    simp only [List.length_cons, List.mem_range, List.getD_cons_succ]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun i hi => ?_, h3⟩
      rcases i with _ | i
      · simpa using h1
      · simpa using h2 i (by simpa using hi)
    · rintro ⟨h2, h3⟩
      refine ⟨by simpa using h2 0 (by omega), fun i hi => ?_, h3⟩
      simpa using h2 (i + 1) (by simpa using hi)

theorem primrec_runI :
    PrimrecPred fun w : List (Trans ℕ) × List ℕ × List (List ℕ) × List ℕ =>
      RunI w.1 w.2.1 w.2.2.1 w.2.2.2 := by
  have hN : Primrec fun w : List (Trans ℕ) × List ℕ × List (List ℕ) × List ℕ => w.1 :=
    Primrec.fst
  have ha : Primrec fun w : List (Trans ℕ) × List ℕ × List (List ℕ) × List ℕ => w.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hms : Primrec fun w : List (Trans ℕ) × List ℕ × List (List ℕ) × List ℕ => w.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec fun w : List (Trans ℕ) × List ℕ × List (List ℕ) × List ℕ => w.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hams : Primrec fun w : List (Trans ℕ) × List ℕ × List (List ℕ) × List ℕ =>
      w.2.1 :: w.2.2.1 := Primrec.list_cons.comp ha hms
  have hlast : Primrec fun w : List (Trans ℕ) × List ℕ × List (List ℕ) × List ℕ =>
      (w.2.1 :: w.2.2.1).getD w.2.2.1.length [] :=
    (Primrec.list_getD []).comp hams (Primrec.list_length.comp hms)
  refine PrimrecPred.and ?_ (PrimrecPred.and ?_ ?_)
  · refine primrecPred_forall_mem (Primrec.list_range.comp (Primrec.list_length.comp hms)) ?_
    exact primrec_fireL.comp (Primrec.pair (hN.comp Primrec.fst) (Primrec.pair
      ((Primrec.list_getD []).comp (hams.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD []).comp (hms.comp Primrec.fst) Primrec.snd)))
  · exact primrec_leL.comp (Primrec.pair hlast hb)
  · exact primrec_leL.comp (Primrec.pair hb hlast)

/-- **Petri net reachability is recursively enumerable.** -/
theorem reach_re :
    REPred fun x : List (Trans ℕ) × List ℕ × List ℕ =>
      Reach x.1 (x.2.1 : Multiset ℕ) (x.2.2 : Multiset ℕ) := by
  have h := rePred_exists (α := List (Trans ℕ) × List ℕ × List ℕ) (β := List (List ℕ))
    (q := fun x ms => RunI x.1 x.2.1 ms x.2.2) (primrec_runI.comp (Primrec.pair
      (Primrec.fst.comp Primrec.fst) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp
        Primrec.fst)) (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp
          Primrec.fst))))))
  refine h.of_eq fun x => ?_
  rw [reach_iff_exists_runL]
  simp only [runL_iff_runI]

/-- **Petri net coverability is recursively enumerable**: some marking `≥ m₁` is reachable. -/
theorem cover_re :
    REPred fun x : List (Trans ℕ) × List ℕ × List ℕ =>
      ∃ m, (x.2.2 : Multiset ℕ) ≤ m ∧ Reach x.1 (x.2.1 : Multiset ℕ) m := by
  have h := rePred_exists (α := List (Trans ℕ) × List ℕ × List ℕ)
    (β := List ℕ × List (List ℕ))
    (q := fun x w => LeL x.2.2 w.1 ∧ RunI x.1 x.2.1 w.2 w.1)
    (PrimrecPred.and (primrec_leL.comp (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp
      Primrec.fst)) (Primrec.fst.comp Primrec.snd)))
      (primrec_runI.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.pair
          (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))))))
  refine h.of_eq fun x => ?_
  constructor
  · rintro ⟨⟨l, ms⟩, hle, hr⟩
    exact ⟨l, leL_iff.1 hle, reach_iff_exists_runL.2 ⟨ms, runL_iff_runI.2 hr⟩⟩
  · rintro ⟨m, hle, hr⟩
    rw [← Multiset.coe_toList m] at hle hr
    obtain ⟨ms, hms⟩ := reach_iff_exists_runL.1 hr
    exact ⟨⟨m.toList, ms⟩, leL_iff.2 hle, runL_iff_runI.1 hms⟩

end Petri

end HTN
