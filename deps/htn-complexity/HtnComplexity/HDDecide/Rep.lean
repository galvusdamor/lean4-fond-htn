import HtnComplexity.HDDecide.Pieces
/-!
# Task networks represented by pieces

`HTN.HD.RepW d q tn T M U inst loc kind` says that the tasks `T` of the semantic task network
`tn` form a disjoint union of the pieces `M`: every task `t ∈ T` belongs to the *copy*
`inst t ∈ U`, which is a copy of the described task network with index `kind (inst t)`, and is
the copy of its identifier `loc t`; labels agree, and two tasks are ordered iff they belong to
the same copy and their identifiers are ordered there.  The multiset `M` collects, for every
copy, the identifiers still present.

The lemmas are the operations of the search on pieces: finding the task of a piece, removing a
task, and replacing an isolated task by a fresh copy of a method's network.
-/

namespace HTN

namespace HD

open Syn

variable (d : DomDesc) (q : InstDesc)

/-- The identifiers of the copy `i` that are still present among the tasks `T`. -/
def Sof (T : Finset ℕ) (inst loc : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  (T.filter (fun t => inst t = i)).image loc

/-- **The representation relation**, with its witnesses. -/
structure RepW (tn : TaskNetwork ℕ ℕ ℕ) (T : Finset ℕ) (M : Multiset Piece) (U : Finset ℕ)
    (inst loc kind : ℕ → ℕ) : Prop where
  inU : ∀ t ∈ T, inst t ∈ U
  inj : ∀ t ∈ T, ∀ t' ∈ T, inst t = inst t' → loc t = loc t' → t = t'
  mem : ∀ t ∈ T, loc t ∈ (net d q (kind (inst t))).ids
  lbl : ∀ t ∈ T, tn.α t = (net d q (kind (inst t))).label (loc t)
  ord : ∀ t ∈ T, ∀ t' ∈ T,
    (tn.ord t t' ↔ inst t = inst t' ∧ ordK d q (kind (inst t)) (loc t) (loc t'))
  eq : M = ∑ i ∈ U, piece (kind i) (Sof T inst loc i)

/-- **The representation relation.** -/
def Rep (tn : TaskNetwork ℕ ℕ ℕ) (T : Finset ℕ) (M : Multiset Piece) : Prop :=
  ∃ U inst loc kind, RepW d q tn T M U inst loc kind

variable {d q}

theorem mem_Sof {T : Finset ℕ} {inst loc : ℕ → ℕ} {i y : ℕ} :
    y ∈ Sof T inst loc i ↔ ∃ t ∈ T, inst t = i ∧ loc t = y := by
  simp [Sof, and_assoc]

theorem piece_eq_singleton {k : ℕ} {S : Finset ℕ} (h : S.Nonempty) : piece k S = {(k, S)} := by
  simp [piece, h.ne_empty]

theorem mem_piece {k : ℕ} {S : Finset ℕ} {p : Piece} : p ∈ piece k S ↔ S ≠ ∅ ∧ p = (k, S) := by
  unfold piece
  split_ifs with h <;> simp [h]

theorem Sof_erase {T : Finset ℕ} {inst loc : ℕ → ℕ}
    (hinj : ∀ t ∈ T, ∀ t' ∈ T, inst t = inst t' → loc t = loc t' → t = t') {t : ℕ} (ht : t ∈ T)
    (i : ℕ) : Sof (T.erase t) inst loc i =
      if i = inst t then (Sof T inst loc i).erase (loc t) else Sof T inst loc i := by
  ext y
  split_ifs with hi
  · subst hi
    simp only [mem_Sof, Finset.mem_erase]
    constructor
    · rintro ⟨t', ⟨hne, ht'⟩, hi', rfl⟩
      exact ⟨fun he => hne (hinj t' ht' t ht hi' he), t', ht', hi', rfl⟩
    · rintro ⟨hy, t', ht', hi', rfl⟩
      exact ⟨t', ⟨fun he => hy (by rw [he]), ht'⟩, hi', rfl⟩
  · simp only [mem_Sof, Finset.mem_erase]
    constructor
    · rintro ⟨t', ⟨-, ht'⟩, hi', rfl⟩
      exact ⟨t', ht', hi', rfl⟩
    · rintro ⟨t', ht', hi', rfl⟩
      exact ⟨t', ⟨by rintro rfl; exact hi hi'.symm, ht'⟩, hi', rfl⟩

namespace RepW

variable {tn : TaskNetwork ℕ ℕ ℕ} {T : Finset ℕ} {M : Multiset Piece} {U : Finset ℕ}
  {inst loc kind : ℕ → ℕ}

theorem loc_mem_Sof {t : ℕ} (ht : t ∈ T) : loc t ∈ Sof T inst loc (inst t) :=
  mem_Sof.2 ⟨t, ht, rfl, rfl⟩

theorem mem_M (h : RepW d q tn T M U inst loc kind) {t : ℕ} (ht : t ∈ T) :
    (kind (inst t), Sof T inst loc (inst t)) ∈ M := by
  rw [h.eq, Multiset.mem_sum]
  refine ⟨inst t, h.inU t ht, ?_⟩
  rw [piece_eq_singleton ⟨_, loc_mem_Sof ht⟩]
  exact Multiset.mem_singleton_self _

theorem exists_of_mem (h : RepW d q tn T M U inst loc kind) {k : ℕ} {S : Finset ℕ} {x : ℕ}
    (hm : (k, S) ∈ M) (hx : x ∈ S) :
    ∃ t ∈ T, kind (inst t) = k ∧ Sof T inst loc (inst t) = S ∧ loc t = x := by
  rw [h.eq, Multiset.mem_sum] at hm
  obtain ⟨i, -, hi⟩ := hm
  obtain ⟨-, he⟩ := mem_piece.1 hi
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨t, ht, rfl, rfl⟩ := mem_Sof.1 hx
  exact ⟨t, ht, rfl, rfl, rfl⟩

theorem eq_zero_iff (h : RepW d q tn T M U inst loc kind) : M = 0 ↔ T = ∅ := by
  constructor
  · intro hM
    by_contra hT
    obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 hT
    have := h.mem_M ht
    rw [hM] at this
    simp at this
  · intro hT
    rw [h.eq]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : Sof T inst loc i = ∅ := by simp [Sof, hT]
    simp [piece, this]

/-- Removing a task from the represented tasks removes its identifier from its piece. -/
theorem sum_erase (h : RepW d q tn T M U inst loc kind) {t : ℕ} (ht : t ∈ T) :
    ∑ i ∈ U, piece (kind i) (Sof (T.erase t) inst loc i) =
      M.erase (kind (inst t), Sof T inst loc (inst t)) +
        piece (kind (inst t)) ((Sof T inst loc (inst t)).erase (loc t)) := by
  have hU := h.inU t ht
  have hne : (Sof T inst loc (inst t)).Nonempty := ⟨_, loc_mem_Sof ht⟩
  rw [h.eq, ← Finset.add_sum_erase U _ hU, ← Finset.add_sum_erase U _ hU,
    piece_eq_singleton hne, Sof_erase h.inj ht, if_pos rfl]
  have hrest : ∑ x ∈ U.erase (inst t), piece (kind x) (Sof (T.erase t) inst loc x) =
      ∑ x ∈ U.erase (inst t), piece (kind x) (Sof T inst loc x) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Sof_erase h.inj ht, if_neg (Finset.ne_of_mem_erase hi)]
  rw [hrest, Multiset.singleton_add, Multiset.erase_cons_head, add_comm]

/-- **Removing a task.** -/
theorem erase (h : RepW d q tn T M U inst loc kind) {t : ℕ} (ht : t ∈ T) :
    RepW d q tn (T.erase t) (M.erase (kind (inst t), Sof T inst loc (inst t)) +
        piece (kind (inst t)) ((Sof T inst loc (inst t)).erase (loc t))) U inst loc kind where
  inU := fun a ha => h.inU a (Finset.mem_of_mem_erase ha)
  inj := fun a ha b hb => h.inj a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  mem := fun a ha => h.mem a (Finset.mem_of_mem_erase ha)
  lbl := fun a ha => h.lbl a (Finset.mem_of_mem_erase ha)
  ord := fun a ha b hb => h.ord a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  eq := (h.sum_erase ht).symm

/-- **Changing the network outside the represented tasks.** -/
theorem transfer (h : RepW d q tn T M U inst loc kind) {tn' : TaskNetwork ℕ ℕ ℕ}
    (hα : ∀ t ∈ T, tn'.α t = tn.α t) (hord : ∀ t ∈ T, ∀ t' ∈ T, (tn'.ord t t' ↔ tn.ord t t')) :
    RepW d q tn' T M U inst loc kind where
  inU := h.inU
  inj := h.inj
  mem := h.mem
  lbl := fun t ht => (hα t ht).trans (h.lbl t ht)
  ord := fun t ht t' ht' => (hord t ht t' ht').trans (h.ord t ht t' ht')
  eq := h.eq

/-- A task whose identifier is minimal in its piece has no predecessor among the represented
tasks. -/
theorem not_ord_of_min (h : RepW d q tn T M U inst loc kind) {t : ℕ} (ht : t ∈ T)
    (hmin : ∀ y ∈ Sof T inst loc (inst t), ¬ ordK d q (kind (inst t)) y (loc t)) :
    ∀ t' ∈ T, ¬ tn.ord t' t := by
  intro t' ht' hord
  obtain ⟨hi, ho⟩ := (h.ord t' ht' t ht).1 hord
  rw [hi] at ho
  exact hmin (loc t') (mem_Sof.2 ⟨t', ht', hi, rfl⟩) ho

/-- A task whose identifier is maximal in its piece has no successor among the represented
tasks. -/
theorem not_ord_of_max (h : RepW d q tn T M U inst loc kind) {t : ℕ} (ht : t ∈ T)
    (hmax : ∀ y ∈ Sof T inst loc (inst t), ¬ ordK d q (kind (inst t)) (loc t) y) :
    ∀ t' ∈ T, ¬ tn.ord t t' := by
  intro t' ht' hord
  obtain ⟨hi, ho⟩ := (h.ord t ht t' ht').1 hord
  exact hmax (loc t') (mem_Sof.2 ⟨t', ht', hi.symm, rfl⟩) ho

/-- Conversely, a task without predecessors has a minimal identifier in its piece. -/
theorem min_of_not_ord (h : RepW d q tn T M U inst loc kind) {t : ℕ} (ht : t ∈ T)
    (hno : ∀ t' ∈ T, ¬ tn.ord t' t) :
    ∀ y ∈ Sof T inst loc (inst t), ¬ ordK d q (kind (inst t)) y (loc t) := by
  intro y hy ho
  obtain ⟨t', ht', hi, rfl⟩ := mem_Sof.1 hy
  refine hno t' ht' ((h.ord t' ht' t ht).2 ⟨hi, ?_⟩)
  rw [hi]
  exact ho

/-- Conversely, a task without successors has a maximal identifier in its piece. -/
theorem max_of_not_ord (h : RepW d q tn T M U inst loc kind) {t : ℕ} (ht : t ∈ T)
    (hno : ∀ t' ∈ T, ¬ tn.ord t t') :
    ∀ y ∈ Sof T inst loc (inst t), ¬ ordK d q (kind (inst t)) (loc t) y := by
  intro y hy ho
  obtain ⟨t', ht', hi, rfl⟩ := mem_Sof.1 hy
  exact hno t' ht' ((h.ord t ht t' ht').2 ⟨hi.symm, ho⟩)

/-- **Decomposing an isolated task** by a fresh copy `u` of the network with index `j + 1`. -/
theorem decompose (h : RepW d q tn T M U inst loc kind) (hwf : tn.WF) (hT : T ⊆ tn.T)
    {t : ℕ} (ht : t ∈ T) (hiso : ∀ y ∈ T, ¬ tn.ord y t ∧ ¬ tn.ord t y)
    {u : TaskNetwork ℕ ℕ ℕ} (hu : u.WF) {j : ℕ} {σ : ℕ → ℕ}
    (hbij : Set.BijOn σ (u.T : Set ℕ) ((net d q (j + 1)).toTaskNetwork.T : Set ℕ))
    (hord : ∀ a ∈ u.T, ∀ b ∈ u.T,
      (u.ord a b ↔ (net d q (j + 1)).toTaskNetwork.ord (σ a) (σ b)))
    (hα : ∀ a ∈ u.T, u.α a = (net d q (j + 1)).toTaskNetwork.α (σ a))
    (hdisj : Disjoint tn.T u.T) {i' : ℕ} (hi' : i' ∉ U) :
    RepW d q (decomposeWith tn t u) (T.erase t ∪ u.T)
      (M.erase (kind (inst t), Sof T inst loc (inst t)) +
        piece (kind (inst t)) ((Sof T inst loc (inst t)).erase (loc t)) +
        piece (j + 1) (net d q (j + 1)).ids.toFinset)
      (insert i' U) (fun a => if a ∈ u.T then i' else inst a)
      (fun a => if a ∈ u.T then σ a else loc a) (Function.update kind i' (j + 1)) := by
  classical
  have hnotu : ∀ a ∈ T, a ∉ u.T := fun a ha => Finset.disjoint_left.1 hdisj (hT ha)
  have hne : ∀ a ∈ T, inst a ≠ i' := fun a ha he => hi' (he ▸ h.inU a ha)
  have hkind : ∀ a ∈ T, Function.update kind i' (j + 1) (inst a) = kind (inst a) :=
    fun a ha => Function.update_of_ne (hne a ha) _ _
  have hmemT' : ∀ {a}, a ∈ T.erase t ∪ u.T ↔ (a ∈ T ∧ a ≠ t) ∨ a ∈ u.T := by
    intro a
    simp [Finset.mem_union, Finset.mem_erase, and_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases hmemT'.1 ha with ⟨ha, -⟩ | ha
    · simp only [hnotu a ha, ↓reduceIte]
      exact Finset.mem_insert_of_mem (h.inU a ha)
    · simp [ha]
  · intro a ha b hb
    rcases hmemT'.1 ha with ⟨ha, -⟩ | ha <;> rcases hmemT'.1 hb with ⟨hb, -⟩ | hb
    · simp only [hnotu a ha, hnotu b hb, ↓reduceIte]
      exact h.inj a ha b hb
    · simp only [hnotu a ha, hb, ↓reduceIte]
      intro he
      exact absurd he (hne a ha)
    · simp only [hnotu b hb, ha, ↓reduceIte]
      intro he
      exact absurd he.symm (hne b hb)
    · simp only [ha, hb, ↓reduceIte]
      intro _ hσ
      exact hbij.injOn ha hb hσ
  · intro a ha
    rcases hmemT'.1 ha with ⟨ha, -⟩ | ha
    · rw [if_neg (hnotu a ha), if_neg (hnotu a ha), hkind a ha]
      exact h.mem a ha
    · rw [if_pos ha, if_pos ha, Function.update_self]
      have := hbij.mapsTo ha
      simpa using this
  · intro a ha
    rcases hmemT'.1 ha with ⟨ha, -⟩ | ha
    · rw [decomposeWith_α, if_neg (hnotu a ha), if_neg (hnotu a ha), if_neg (hnotu a ha),
        hkind a ha]
      exact h.lbl a ha
    · rw [decomposeWith_α, if_pos ha, if_pos ha, if_pos ha, Function.update_self]
      exact hα a ha
  · intro a ha b hb
    rw [decomposeWith_ord_iff]
    have hnt : ∀ {x y : ℕ}, x ∉ tn.T → ¬ tn.ord x y := fun hx ho => hx (hwf.mem_left ho)
    have hnt' : ∀ {x y : ℕ}, y ∉ tn.T → ¬ tn.ord x y := fun hy ho => hy (hwf.mem_right ho)
    have hnu : ∀ {x y : ℕ}, x ∉ u.T → ¬ u.ord x y := fun hx ho => hx (hu.mem_left ho)
    have hnu' : ∀ {x y : ℕ}, y ∉ u.T → ¬ u.ord x y := fun hy ho => hy (hu.mem_right ho)
    have hut : ∀ {x}, x ∈ u.T → x ∉ tn.T := fun hx hx' => Finset.disjoint_left.1 hdisj hx' hx
    rcases hmemT'.1 ha with ⟨ha, hat⟩ | ha <;> rcases hmemT'.1 hb with ⟨hb, hbt⟩ | hb
    · simp only [if_neg (hnotu a ha), if_neg (hnotu b hb)]
      rw [show (if a ∈ u.T then i' else inst a) = inst a from if_neg (hnotu a ha), hkind a ha,
        ← h.ord a ha b hb]
      constructor
      · rintro (ho | ⟨-, hb'⟩ | ⟨-, ha'⟩ | ⟨ho, -, -⟩)
        · exact absurd ho (hnu (hnotu a ha))
        · exact absurd hb' (hnotu b hb)
        · exact absurd ha' (hnotu a ha)
        · exact ho
      · intro ho
        exact Or.inr (Or.inr (Or.inr ⟨ho, hat, hbt⟩))
    · simp only [if_neg (hnotu a ha), if_pos hb]
      refine iff_of_false ?_ ?_
      · rintro (ho | ⟨ho, -⟩ | ⟨-, ha'⟩ | ⟨ho, -, -⟩)
        · exact hnu (hnotu a ha) ho
        · exact (hiso a ha).1 ho
        · exact hnotu a ha ha'
        · exact hnt' (hut hb) ho
      · rintro ⟨he, -⟩
        exact hne a ha he
    · simp only [if_neg (hnotu b hb), if_pos ha]
      refine iff_of_false ?_ ?_
      · rintro (ho | ⟨-, hb'⟩ | ⟨ho, -⟩ | ⟨ho, -, -⟩)
        · exact hnu' (hnotu b hb) ho
        · exact hnotu b hb hb'
        · exact (hiso b hb).2 ho
        · exact hnt (hut ha) ho
      · rintro ⟨he, -⟩
        exact hne b hb he.symm
    · simp only [if_pos ha, if_pos hb]
      rw [show (if a ∈ u.T then i' else inst a) = i' from if_pos ha, Function.update_self]
      simp only [true_and, ordK]
      rw [← hord a ha b hb]
      constructor
      · rintro (ho | ⟨ho, -⟩ | ⟨ho, -⟩ | ⟨ho, -, -⟩)
        · exact ho
        · exact absurd ho (hnt (hut ha))
        · exact absurd ho (hnt' (hut hb))
        · exact absurd ho (hnt (hut ha))
      · exact fun ho => Or.inl ho
  · -- the multiset of pieces
    rw [Finset.sum_insert hi', Function.update_self]
    have hSi' : Sof (T.erase t ∪ u.T) (fun a => if a ∈ u.T then i' else inst a)
        (fun a => if a ∈ u.T then σ a else loc a) i' = (net d q (j + 1)).ids.toFinset := by
      ext y
      rw [mem_Sof]
      constructor
      · rintro ⟨a, ha, hia, rfl⟩
        rcases hmemT'.1 ha with ⟨ha, -⟩ | ha
        · simp only [hnotu a ha, ↓reduceIte] at hia
          exact absurd hia (hne a ha)
        · simp only [ha, ↓reduceIte]
          have := hbij.mapsTo ha
          simpa using this
      · intro hy
        have hy' : y ∈ ((net d q (j + 1)).toTaskNetwork.T : Set ℕ) := by simpa using hy
        rw [← hbij.image_eq] at hy'
        obtain ⟨a, ha, rfl⟩ := hy'
        exact ⟨a, Finset.mem_union_right _ ha, by simp [show a ∈ u.T from ha],
          by simp [show a ∈ u.T from ha]⟩
    have hrest : ∀ i ∈ U, piece (Function.update kind i' (j + 1) i)
        (Sof (T.erase t ∪ u.T) (fun a => if a ∈ u.T then i' else inst a)
          (fun a => if a ∈ u.T then σ a else loc a) i) =
        piece (kind i) (Sof (T.erase t) inst loc i) := by
      intro i hi
      have hii : i ≠ i' := fun he => hi' (he ▸ hi)
      rw [Function.update_of_ne hii]
      congr 1
      ext y
      simp only [mem_Sof]
      constructor
      · rintro ⟨a, ha, hia, rfl⟩
        rcases hmemT'.1 ha with ⟨ha', hat⟩ | ha'
        · simp only [hnotu a ha', ↓reduceIte] at hia ⊢
          exact ⟨a, Finset.mem_erase.2 ⟨hat, ha'⟩, hia, rfl⟩
        · simp only [ha', ↓reduceIte] at hia
          exact absurd hia.symm hii
      · rintro ⟨a, ha, hia, rfl⟩
        have ha' := Finset.mem_of_mem_erase ha
        refine ⟨a, Finset.mem_union_left _ ha, ?_, ?_⟩ <;> simp [hnotu a ha', hia]
    rw [Finset.sum_congr rfl hrest, h.sum_erase ht, hSi']
    abel

end RepW

/-- **The initial network is represented by the initial pieces.** -/
theorem repW_init :
    RepW d q q.tnI.toTaskNetwork q.tnI.ids.toFinset (initPieces q) {0} (fun _ => 0) id
      (fun _ => 0) where
  inU := by simp
  inj := fun _ _ _ _ _ h => h
  mem := fun t ht => by simpa [net] using ht
  lbl := fun t _ => rfl
  ord := fun t _ t' _ => by simp [ordK, net]
  eq := by
    have : Sof q.tnI.ids.toFinset (fun _ => 0) id 0 = q.tnI.ids.toFinset := by
      ext y
      simp [mem_Sof]
    simp [initPieces, this]

end HD

end HTN
