import HtnComplexity.Article.PlanEx
import HtnComplexity.PT.Arith
/-!
# Well-formedness of descriptions is decidable in polynomial time

* `HTN.Article.validB` — a Boolean test, `HTN.Article.validB_iff`: it decides
  `HTN.Article.ProbDesc.Valid`;
* `HTN.Article.pt_validB` — it is a polynomial-time function in the typed calculus of
  `HtnComplexity/PT/`;
* `HTN.Article.PT.primrec_of_bool` — a polynomial-time Boolean function is primitive recursive, so
  in particular `HTN.Article.primrec_validB`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom

/-! ### Boolean tests -/

/-- The list has no duplicates. -/
def nodupB (l : List ℕ) : Bool := l.all fun a => l.count a == 1

/-- The two lists are permutations of each other. -/
def permB (l l' : List ℕ) : Bool := (l ++ l').all fun a => l.count a == l'.count a

theorem nodupB_iff (l : List ℕ) : nodupB l = true ↔ l.Nodup := by
  rw [List.nodup_iff_count_le_one]
  simp only [nodupB, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h a
    by_cases ha : a ∈ l
    · exact (h a ha).le
    · rw [List.count_eq_zero_of_not_mem ha]; omega
  · intro h a ha
    have h1 := h a
    have h2 := List.count_pos_iff.2 ha
    omega

theorem permB_iff (l l' : List ℕ) : permB l l' = true ↔ l.Perm l' := by
  rw [List.perm_iff_count]
  simp only [permB, List.all_eq_true, beq_iff_eq, List.mem_append]
  constructor
  · intro h a
    by_cases ha : a ∈ l ∨ a ∈ l'
    · exact h a ha
    · push_neg at ha
      rw [List.count_eq_zero_of_not_mem ha.1, List.count_eq_zero_of_not_mem ha.2]
  · intro h a _
    exact h a

/-- **The test for task network descriptions.** -/
def tnValidB (decl : List ℕ) (t : TnDesc) : Bool :=
  nodupB t.ids &&
  t.ordList.all (fun q => decide (q.1 ∈ t.ids) && decide (q.2 ∈ t.ids)) &&
  t.ordList.all (fun q => !(q.1 == q.2)) &&
  t.ordList.all (fun x => t.ordList.all fun y =>
    !(x.2 == y.1) || t.ordList.any fun z => z.1 == x.1 && z.2 == y.2) &&
  permB (t.lbl.map Prod.fst) t.ids &&
  t.lbl.all (fun q => q.2.1 || decide (q.2.2 ∈ decl))

/-- **The test for problem descriptions.** -/
def validB (p : ProbDesc) : Bool :=
  nodupB (p.actions.map ActDesc.name) &&
  tnValidB (p.actions.map ActDesc.name) p.tnI &&
  p.methods.all fun m => tnValidB (p.actions.map ActDesc.name) m.2

theorem tnValidB_iff (decl : List ℕ) (t : TnDesc) :
    tnValidB decl t = true ↔ TnValid (· ∈ decl) t := by
  have hany : ∀ (l : List (ℕ × ℕ)) (a b : ℕ),
      (l.any fun z => z.1 == a && z.2 == b) = true ↔ (a, b) ∈ l := by
    intro l a b
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨z, hz, h1, h2⟩; rw [← h1, ← h2]; exact hz
    · intro h; exact ⟨(a, b), h, rfl, rfl⟩
  simp only [tnValidB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, nodupB_iff,
    permB_iff, Bool.not_eq_true', beq_eq_false_iff_ne, Bool.or_eq_true, ne_eq, hany]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    refine ⟨h1, h2, fun a ha => h3 _ ha rfl, fun a b c hab hbc => ?_, h5, fun q hq hq' => ?_⟩
    · rcases h4 _ hab _ hbc with h | h
      · simp at h
      · exact h
    · rcases h6 q hq with h | h
      · rw [hq'] at h; simp at h
      · exact h
  · intro h
    refine ⟨⟨⟨⟨⟨h.nodup, h.ord_mem⟩, fun q hq heq => h.irrefl q.1 ?_⟩, fun x hx y hy => ?_⟩,
      h.lbl_perm⟩, fun q hq => ?_⟩
    · have : q = (q.1, q.1) := Prod.ext rfl heq.symm
      rw [this] at hq; exact hq
    · by_cases hxy : x.2 = y.1
      · refine Or.inr (h.trans _ _ _ hx ?_)
        rw [hxy]; exact hy
      · exact Or.inl hxy
    · by_cases hb : q.2.1 = true
      · exact Or.inl hb
      · exact Or.inr (h.prim_ok q hq (by simpa using hb))

/-- **`validB` decides well-formedness.** -/
theorem validB_iff (p : ProbDesc) : validB p = true ↔ p.Valid := by
  simp only [validB, Bool.and_eq_true, List.all_eq_true, nodupB_iff, tnValidB_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun m hm => h3 m hm⟩
  · intro h
    exact ⟨⟨h.names_nodup, h.tnI⟩, fun m hm => h.methods m hm⟩

instance (p : ProbDesc) : Decidable p.Valid := decidable_of_iff _ (validB_iff p)

/-! ### Polynomial time -/

theorem pt_count {α : Type} [BEnc α] {f : α → List ℕ} {g : α → ℕ} (hf : PT f) (hg : PT g) :
    PT fun a => (f a).count (g a) := by
  refine (PT.length (PT.filter (p := fun a b => b == g a) hf
    (PT.beq PT.snd (hg.comp PT.fst)))).of_eq fun a => ?_
  rw [List.count_eq_length_filter]

theorem pt_nodupB {α : Type} [BEnc α] {f : α → List ℕ} (hf : PT f) : PT fun a => nodupB (f a) := by
  unfold nodupB
  exact PT.all hf (PT.beq (pt_count (hf.comp PT.fst) PT.snd) (PT.const 1))

theorem pt_permB {α : Type} [BEnc α] {f g : α → List ℕ} (hf : PT f) (hg : PT g) :
    PT fun a => permB (f a) (g a) := by
  unfold permB
  exact PT.all (PT.append hf hg) (PT.beq (pt_count (hf.comp PT.fst) PT.snd)
    (pt_count (hg.comp PT.fst) PT.snd))

theorem pt_tnValidB : PT₂ tnValidB := by
  unfold PT₂ tnValidB
  have hd : PT fun p : List ℕ × TnDesc => p.1 := PT.fst
  have hids : PT fun p : List ℕ × TnDesc => p.2.ids := PT.fst.comp PT.snd
  have hord : PT fun p : List ℕ × TnDesc => p.2.ordList := PT.fst.comp (PT.snd.comp PT.snd)
  have hlbl : PT fun p : List ℕ × TnDesc => p.2.lbl := PT.snd.comp (PT.snd.comp PT.snd)
  refine PT.and (PT.and (PT.and (PT.and (PT.and (pt_nodupB hids) ?_) ?_) ?_) ?_) ?_
  · exact PT.all hord (PT.and (PT.elem (hids.comp PT.fst) (PT.fst.comp PT.snd))
      (PT.elem (hids.comp PT.fst) (PT.snd.comp PT.snd)))
  · exact PT.all hord (PT.not (PT.beq (PT.fst.comp PT.snd) (PT.snd.comp PT.snd)))
  · refine PT.all hord ?_
    refine PT.all (hord.comp PT.fst) ?_
    exact PT.or (PT.not (PT.beq (PT.snd.comp (PT.snd.comp PT.fst)) (PT.fst.comp PT.snd)))
      (PT.any (hord.comp (PT.fst.comp PT.fst))
        (PT.and (PT.beq (PT.fst.comp PT.snd) (PT.fst.comp (PT.snd.comp (PT.fst.comp PT.fst))))
          (PT.beq (PT.snd.comp PT.snd) (PT.snd.comp (PT.snd.comp PT.fst)))))
  · exact pt_permB (PT.map hlbl (PT.fst.comp PT.snd)) hids
  · exact PT.all hlbl (PT.or (PT.fst.comp (PT.snd.comp PT.snd))
      (PT.elem (hd.comp PT.fst) (PT.snd.comp (PT.snd.comp PT.snd))))

/-- **Well-formedness is decidable in polynomial time.** -/
theorem pt_validB : PT validB := by
  unfold validB
  have hn : PT fun p : ProbDesc => p.actions.map ActDesc.name :=
    PT.map (PT.fst.comp PT.fst) (PT.fst.comp PT.snd)
  refine PT.and (PT.and (pt_nodupB hn) (PT.comp₂ pt_tnValidB hn (PT.fst.comp (PT.snd.comp PT.snd)))) ?_
  exact PT.all (PT.snd.comp PT.fst)
    (PT.comp₂ pt_tnValidB (hn.comp PT.fst) (PT.snd.comp PT.snd))

/-! ### From polynomial time to primitive recursion -/

/-- A Boolean function of the typed polynomial-time calculus is primitive recursive (on a type
whose encoding is). -/
theorem PT.primrec_of_bool {α : Type} [BEnc α] [Primcodable α] [PEnc α] {f : α → Bool}
    (hf : PT f) : Primrec f := by
  obtain ⟨F, hF, hFf⟩ := hf
  have hc : Primrec fun a : α => F (enc a) := by
    have h1 : Primrec fun x : List Bool => F x := by
      have := (hF.primrec).comp (Primrec.list_cons.comp Primrec.id (Primrec.const []))
      simpa using this
    exact h1.comp PEnc.primrec_enc
  refine (Primrec.list_headI.comp hc).of_eq fun a => ?_
  rw [hFf a]
  rfl

theorem primrec_validB : Primrec validB := PT.primrec_of_bool pt_validB

end Article

end HTN
