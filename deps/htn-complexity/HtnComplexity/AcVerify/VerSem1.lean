import HtnComplexity.AcVerify.VerRec
/-!
# Semantics of the verifier, part 1: parsing, entries, roots

* list lemmas (quantifying over the decompositions `l = l₁ ++ a :: l₂`);
* `HTN.Syn.AcVer.CE` — a parsed entry of the certificate, and the parsing step of the verifier
  (`exists_certOf_acV`);
* `HTN.Syn.AcVer.recsB_iff` — the record test of an entry whose records are the records of a step
  list `p`, as a condition on `p`;
* `HTN.Syn.AcVer.rootsB_iff` — the root completeness test.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space

/-! ### Decompositions of lists -/

theorem forall_split_map {α β : Type} (g : α → β) (p : List α)
    (Q : List β → β → List β → Prop) :
    (∀ l₁ w l₂, p.map g = l₁ ++ w :: l₂ → Q l₁ w l₂) ↔
      ∀ l₁ x l₂, p = l₁ ++ x :: l₂ → Q (l₁.map g) (g x) (l₂.map g) := by
  constructor
  · rintro h l₁ x l₂ rfl
    exact h _ _ _ (by simp)
  · intro h l₁ w l₂ he
    obtain ⟨a, b, rfl, ha, hb⟩ := List.map_eq_append_iff.1 he
    obtain ⟨x, c, rfl, hx, hc⟩ := List.map_eq_cons_iff.1 hb
    rw [← ha, ← hx, ← hc]
    exact h a x c rfl

theorem isChain_of_splits {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, (∀ l₁ a b l₂, l = l₁ ++ a :: b :: l₂ → R a b) → l.IsChain R
  | [], _ => List.IsChain.nil
  | [_], _ => List.isChain_singleton _
  | a :: b :: l, h => by
    refine List.IsChain.cons_cons (h [] a b l rfl) (isChain_of_splits fun l₁ c e l₂ he => ?_)
    exact h (a :: l₁) c e l₂ (by rw [he]; rfl)

theorem splits_of_isChain {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.IsChain R → ∀ l₁ a b l₂, l = l₁ ++ a :: b :: l₂ → R a b
  | [], _, l₁, _, _, _, he => by simp at he
  | [_], _, l₁, a, b, l₂, he => by
    rcases l₁ with _ | ⟨c, l₁⟩ <;> simp at he
  | x :: y :: l, h, l₁, a, b, l₂, he => by
    rcases l₁ with _ | ⟨c, l₁⟩
    · simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      exact (List.isChain_cons_cons.1 h).1
    · simp only [List.cons_append, List.cons.injEq] at he
      exact splits_of_isChain (List.isChain_cons_cons.1 h).2 l₁ a b l₂ he.2

theorem pairwise_iff_splits {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R ↔ ∀ l₁ a l₂, l = l₁ ++ a :: l₂ → ∀ b ∈ l₂, R a b
  | [] => by simp
  | x :: l => by
    rw [List.pairwise_cons, pairwise_iff_splits]
    constructor
    · rintro ⟨h1, h2⟩ l₁ a l₂ he b hb
      rcases l₁ with _ | ⟨c, l₁⟩
      · simp only [List.nil_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact h1 b hb
      · simp only [List.cons_append, List.cons.injEq] at he
        exact h2 l₁ a l₂ he.2 b hb
    · intro h
      exact ⟨fun b hb => h [] x l rfl b hb, fun l₁ a l₂ he b hb =>
        h (x :: l₁) a l₂ (by rw [he]; rfl) b hb⟩

theorem forall_mem_iff_splits {α : Type} {P : α → Prop} {l : List α} :
    (∀ a ∈ l, P a) ↔ ∀ l₁ a l₂, l = l₁ ++ a :: l₂ → P a := by
  constructor
  · rintro h l₁ a l₂ rfl; exact h a (by simp)
  · intro h a ha
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
    exact h l₁ a l₂ rfl

theorem entriesEnc_eq_nil {l : List (List Bool)} : entriesEnc l = [] ↔ l = [] := by
  cases l <;> simp [entriesEnc]

/-! ### Parsed entries -/

/-- **A parsed entry of the certificate.** -/
structure CE where
  recs : List (List Bool)
  st : List (List Bool)
  pr : List (List Bool)
  ad : List (List Bool)
  de : List (List Bool)
  f : Bool

/-- The content of a parsed entry. -/
def CE.enc (e : CE) : List Bool := encEnt e.recs e.st e.pr e.ad e.de e.f

theorem CE.enc_eq (e : CE) :
    e.enc = blist e.recs ++ (blist e.st ++ (blist e.pr ++ (blist e.ad ++ (blist e.de ++ [e.f])))) :=
  rfl

@[simp] theorem CE.flagOf_enc (e : CE) : flagOf e.enc = e.f := flagOf_encEnt _ _ _ _ _ _

@[simp] theorem CE.stOf_enc (e : CE) :
    stOf e.enc = blist e.st ++ (blist e.pr ++ (blist e.ad ++ (blist e.de ++ [e.f]))) :=
  stOf_encEnt _ _ _ _ _ _

theorem entAll_mem (P : List Bool → Bool) (l : List (List Bool)) (z : List Bool) :
    entAll (blist l ++ z) (fun _ E _ => P E) = true ↔ ∀ c ∈ l, P (true :: bstr c) = true := by
  rw [entAll_iff, forall_mem_iff_splits]

theorem exists_map_of_forall {α β : Type} {g : α → β} :
    ∀ {l : List β}, (∀ c ∈ l, ∃ e, g e = c) → ∃ cs : List α, l = cs.map g
  | [], _ => ⟨[], rfl⟩
  | c :: l, h => by
    obtain ⟨e, he⟩ := h c (by simp)
    obtain ⟨cs, hcs⟩ := exists_map_of_forall (l := l) fun c' hc' => h c' (by simp [hc'])
    exact ⟨e :: cs, by rw [List.map_cons, he, hcs]⟩

/-- **The parsing step**: a certificate accepted by the parse test is the serialised list of the
contents of parsed entries. -/
theorem exists_ces {w : List Bool} (hw : blistB w = true)
    (hp : ∀ c, (∃ l z, w = blist l ++ z ∧ c ∈ l) → parseB c = true) :
    ∃ cs : List CE, w = blist (cs.map CE.enc) := by
  obtain ⟨l, rfl⟩ := blistB_iff.1 hw
  have h : ∀ c ∈ l, ∃ e : CE, e.enc = c := fun c hc => by
    obtain ⟨recs, st, pr, ad, de, f, he⟩ := eq_encEnt_of_parseB (hp c ⟨l, [], by simp, hc⟩)
    exact ⟨⟨recs, st, pr, ad, de, f⟩, he.symm⟩
  obtain ⟨cs, hcs⟩ := exists_map_of_forall h
  exact ⟨cs, by rw [hcs]⟩

/-! ### Steps, records, and the record test -/

/-- A method step: a task of the network of a listed method. -/
def IsMStep (d : DomDesc) (x : PStep) : Prop :=
  x.1 ∈ mIdx d ∧ x.2 ∈ (methodAt d x.1).2.ids

/-- The dummy step of a listed method with an empty network. -/
def IsDummy (d : DomDesc) (x : PStep) : Prop :=
  x.1 ∈ mIdx d ∧ (methodAt d x.1).2.ids = [] ∧ x.2 = 0

theorem advOf_eq (d : DomDesc) :
    advOf d = blist (mstepT d) ++
      (blist (dummyT d) ++ (blist (headT d) ++ (blist (ordT d) ++ blist (actT d)))) := by
  simp only [advOf, List.append_assoc]

theorem occB_mstep (d : DomDesc) (q : InstDesc) (x : PStep) :
    occB (advOf d) (true :: bstr (recOf d q x)) = true ↔ IsMStep d x := by
  rw [advOf_eq, occB_iff, mem_mstepT]
  constructor
  · rintro ⟨k, hk, j, hj, he⟩
    rw [← recOf_mem_of_mIdx (q := q) (x := (k, j)) hk] at he
    rw [recOf_injective d q he]
    exact ⟨hk, hj⟩
  · rintro ⟨hk, hj⟩
    exact ⟨x.1, hk, x.2, hj, recOf_mem_of_mIdx hk⟩

theorem occB_dummy (d : DomDesc) (q : InstDesc) (x : PStep) :
    occB (tD (advOf d)) (true :: bstr (recOf d q x)) = true ↔ IsDummy d x := by
  rw [tD_advOf, List.append_assoc, List.append_assoc, occB_iff, mem_dummyT]
  constructor
  · rintro ⟨k, hk, he, hR⟩
    rw [← recOf_mem_of_mIdx (q := q) (x := (k, 0)) hk] at hR
    rw [recOf_injective d q hR]
    exact ⟨hk, he, rfl⟩
  · rintro ⟨hk, he, h0⟩
    refine ⟨x.1, hk, he, ?_⟩
    rw [recOf_mem_of_mIdx hk]
    exact congrArg _ (Prod.ext rfl h0)

/-- The condition the record test puts on the step `x` of a path `l₁ ++ x :: l₂` of an entry
with flag `f`. -/
def RecBody (d : DomDesc) (q : InstDesc) (f : Bool) (l₁ : List PStep) (x : PStep)
    (l₂ : List PStep) : Prop :=
  (l₁ = [] ∨ IsMStep d x ∨ (l₂ = [] ∧ f = true ∧ IsDummy d x)) ∧
    (∀ y l₂', l₂ = y :: l₂' → Link d q x y) ∧
    (l₂ = [] → (f = true ∨ lTag (stepLabel d q x) = 0) ∧ (f = false ∨ (l₁ ≠ [] ∧ IsDummy d x)))

theorem isLast_blist_map {l : List (List Bool)} {z : List Bool} :
    isLast (blist l ++ z) = true ↔ l = [] := by
  cases l <;> simp [isLast, blist_cons, blist_nil]

theorem hasNext_blist_map {l : List (List Bool)} {z : List Bool} :
    hasNext (blist l ++ z) = true ↔ l ≠ [] := by
  cases l <;> simp [hasNext, blist_cons, blist_nil]

theorem key_ne_key {a b : ℕ} (h : a ≠ b) : key a ≠ key b := fun he => h (key_injective he)

/-- The body of the record test at one record. -/
theorem recBody_iff (d : DomDesc) (q : InstDesc) (c : List Bool) (f : Bool) (hf : flagOf c = f)
    (l₁ : List PStep) (x : PStep) (l₂ : List PStep) (z : List Bool) :
    ((decide (entriesEnc (l₁.map (recOf d q)) = []) ||
        occB (advOf d) (true :: bstr (recOf d q x)) ||
        (isLast (blist (l₂.map (recOf d q)) ++ z) && flagOf c &&
          occB (tD (advOf d)) (true :: bstr (recOf d q x)))) &&
      (!hasNext (blist (l₂.map (recOf d q)) ++ z) ||
        linkB (advOf d) (true :: bstr (recOf d q x))
          (nextEnt (blist (l₂.map (recOf d q)) ++ z))) &&
      (!isLast (blist (l₂.map (recOf d q)) ++ z) ||
        lastB (advOf d) c (entriesEnc (l₁.map (recOf d q))) (true :: bstr (recOf d q x)))) =
      true ↔ RecBody d q f l₁ x l₂ := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    entriesEnc_eq_nil, List.map_eq_nil_iff, isLast_blist_map, hf, occB_mstep,
    occB_dummy, RecBody]
  have hhn : hasNext (blist (l₂.map (recOf d q)) ++ z) = false ↔ l₂ = [] := by
    rw [← Bool.not_eq_true, hasNext_blist_map]; simp
  have hil : isLast (blist (l₂.map (recOf d q)) ++ z) = false ↔ l₂ ≠ [] := by
    rw [← Bool.not_eq_true, isLast_blist_map]; simp
  rw [hhn, hil]
  have hlink : (l₂ = [] ∨ linkB (advOf d) (true :: bstr (recOf d q x))
      (nextEnt (blist (l₂.map (recOf d q)) ++ z)) = true) ↔
      ∀ y l₂', l₂ = y :: l₂' → Link d q x y := by
    rcases l₂ with _ | ⟨y, l₂'⟩
    · simp
    · simp only [List.map_cons, nextEnt_blist, reduceCtorEq, false_or, linkB_iff,
        List.cons.injEq]
      exact ⟨fun h y' l h' => h'.1 ▸ h, fun h => h y l₂' ⟨rfl, rfl⟩⟩
  rw [hlink]
  have hlast : (l₂ ≠ [] ∨ lastB (advOf d) c (entriesEnc (l₁.map (recOf d q)))
      (true :: bstr (recOf d q x)) = true) ↔
      (l₂ = [] → (f = true ∨ lTag (stepLabel d q x) = 0) ∧
        (f = false ∨ (l₁ ≠ [] ∧ IsDummy d x))) := by
    simp only [lastB, Bool.and_eq_true, Bool.or_eq_true, hf, decide_eq_true_eq,
      Bool.not_eq_true', kat2_recOf, entriesEnc_eq_nil, List.map_eq_nil_iff, occB_dummy]
    have hk : key (lTag (stepLabel d q x)) = key 0 ↔ lTag (stepLabel d q x) = 0 :=
      ⟨fun h => key_injective h, fun h => by rw [h]⟩
    rw [hk]
    constructor
    · rintro (h | h) h'
      · exact absurd h' h
      · simpa using h
    · intro h
      by_cases h' : l₂ = []
      · exact Or.inr (by simpa using h h')
      · exact Or.inl h'
  rw [hlast]
  simp only [or_assoc, and_assoc]

theorem enc_eq_recs (e : CE) : e.enc = blist e.recs ++ stOf e.enc := by
  rw [CE.stOf_enc]; rfl

/-- **The record test**, for an entry whose records are those of the step list `p`. -/
theorem recsB_iff (d : DomDesc) (q : InstDesc) (e : CE) (p : List PStep)
    (hp : e.recs = p.map (recOf d q)) :
    recsB (instSer q) (advOf d) e.enc = true ↔
      (∃ i ∈ q.tnI.ids, ∃ s, p = (0, i) :: s) ∧
        ∀ l₁ x l₂, p = l₁ ++ x :: l₂ → RecBody d q e.f l₁ x l₂ := by
  unfold recsB
  rw [enc_eq_recs e, hp]
  simp only [Bool.and_eq_true]
  rw [entAll_iff]
  rw [forall_split_map (recOf d q) p (fun l₁ w l₂ => _ = true)]
  have hf : flagOf (blist (p.map (recOf d q)) ++ stOf e.enc) = e.f := by
    rw [← hp, ← enc_eq_recs]; simp
  refine and_congr ?_ (forall₃_congr fun l₁ x l₂ => imp_congr_right fun _ =>
    recBody_iff d q _ e.f hf l₁ x l₂ _)
  rcases p with _ | ⟨x₀, s⟩
  · simp [blist_nil]
  · rw [List.map_cons, nextEnt_blist, rootRecB_iff d q]
    simp only [blist_cons, List.cons_append, List.headD_cons, true_and, List.cons.injEq]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, s, recOf_injective d q (bstr_parse (r := []) (s := []) (by simpa using h)).1, rfl⟩
    · rintro ⟨i, hi, s', h, -⟩
      exact ⟨i, hi, by rw [h]⟩

end AcVer

end Syn

end HTN
