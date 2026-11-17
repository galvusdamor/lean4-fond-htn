import FondHtn.Weak.Desc
/-!
# The weak compilation preserves acyclicity, tail recursion and total order

For a well-formed description `p`, the translation `weakDesc p` is acyclic (tail-recursive,
totally ordered, …) iff `p` is.  The new compound names `2a + 1` (the wrapped primitive tasks) are
placed below all original compound names `2c`, ordered among themselves by `≤`; their methods
contain primitive tasks only.

**Regularity is not preserved**: a regular method `c → ⟨a, c'⟩` becomes `2c → ⟨2a+1, 2c'⟩`
with two compound tasks ([CB21, Cor. 4.5] treats regular problems separately).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.TaskNetwork

variable {p : FProbDesc}

/-- The translation, as a problem of the library. -/
abbrev QP (p : FProbDesc) := (weakDesc p).toProblem.toPos
/-- The skeleton of the FOND problem. -/
abbrev PP (p : FProbDesc) := p.toProblem.toArt.toPos

theorem mem_weakDesc_methods {m' : Method ℕ ℕ ℕ} (hm : m' ∈ (QP p).methods) :
    (∃ e ∈ p.methods, m' = (wrapMD e).toMethod) ∨
      ∃ y ∈ p.actions, ∃ j < y.effs.length,
        m' = MethodDesc.toMethod (2 * y.1 + 1, ([0], [], [(0, false, Nat.pair y.1 j)])) := by
  obtain ⟨e', he', rfl⟩ := hm
  simp only [weakDesc, ProbDesc.methods, List.mem_append, List.mem_map, List.mem_flatMap] at he'
  rcases he' with ⟨e, he, rfl⟩ | ⟨y, hy, hm⟩
  · exact Or.inl ⟨e, he, rfl⟩
  · simp only [leafMDs, List.mem_map, List.mem_range] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    exact Or.inr ⟨y, hy, j, hj, rfl⟩

theorem leaf_label (y : FActDesc) (j t : ℕ) :
    (MethodDesc.toMethod (2 * y.1 + 1, ([0], [], [(0, false, Nat.pair y.1 j)]))).subtasks.α t =
      Sum.inl (if t = 0 then Nat.pair y.1 j else 0) := by
  simp only [MethodDesc.toMethod, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl, List.lookup]
  by_cases ht : t = 0
  · subst ht; simp
  · have : (t == 0) = false := by simp [ht]
    simp [this, ht]

theorem wrapMD_label (hp : p.Valid) {e : MethodDesc} (he : e ∈ p.methods) {t : ℕ}
    (ht : t ∈ (wrapMD e).toMethod.subtasks.T) :
    (wrapMD e).toMethod.subtasks.α t = wE (e.toMethod.subtasks.α t) :=
  label_wrapTn (hp.methods e he) (by simpa [MethodDesc.toMethod, wrapMD, TnDesc.toTaskNetwork,
    wrapTn, TnDesc.ids] using ht)

theorem tnI_label (hp : p.Valid) {t : ℕ} (ht : t ∈ (QP p).tnI.T) : (QP p).tnI.α t = wE ((PP p).tnI.α t) :=
  label_wrapTn hp.tnI (List.mem_toFinset.1 ht)

theorem wE_inr {y : ℕ ⊕ ℕ} {x : ℕ} (h : wE y = Sum.inr x) :
    (∃ c, y = Sum.inr c ∧ x = 2 * c) ∨ (∃ a, y = Sum.inl a ∧ x = 2 * a + 1) := by
  cases y with
  | inl a => right; simp [wE] at h; exact ⟨a, rfl, h.symm⟩
  | inr c => left; simp [wE] at h; exact ⟨c, rfl, h.symm⟩

theorem reach_Q (hp : p.Valid) {x : ℕ} (h : (QP p).ReachableName x) :
    (∃ c, x = 2 * c ∧ (PP p).ReachableName c) ∨ x % 2 = 1 := by
  induction h with
  | @tnI t x ht hx =>
    rw [tnI_label hp ht] at hx
    rcases wE_inr hx with ⟨c, hc, rfl⟩ | ⟨a, -, rfl⟩
    · exact Or.inl ⟨c, rfl, .tnI ht hc⟩
    · right; omega
  | @method m' t x hm hr ht hx ih =>
    rcases mem_weakDesc_methods hm with ⟨e, he, rfl⟩ | ⟨y, -, j, -, rfl⟩
    · rcases ih with ⟨c, hc, hrc⟩ | hodd
      · rw [wrapMD_label hp he ht] at hx
        rcases wE_inr hx with ⟨d, hd, rfl⟩ | ⟨a, -, rfl⟩
        · have hc' : e.1 = c := by simp [wrapMD, MethodDesc.toMethod] at hc; omega
          rw [← hc'] at hrc
          exact Or.inl ⟨d, rfl, .method ⟨e, he, rfl⟩ hrc
            (by simpa [MethodDesc.toMethod, wrapMD, wrapTn, TnDesc.toTaskNetwork, TnDesc.ids]
              using ht) hd⟩
        · right; omega
      · simp [wrapMD, MethodDesc.toMethod] at hodd <;> omega
    · rw [leaf_label] at hx; cases hx

theorem reach_P₀ (hp : p.Valid) {c : ℕ} (h : (PP p).ReachableName c) : (QP p).ReachableName (2 * c) := by
  induction h with
  | @tnI t c ht hc =>
    have ht' : t ∈ (QP p).tnI.T := ht
    exact .tnI ht' (by rw [tnI_label hp ht', hc]; rfl)
  | @method m t c hm hr ht hc ih =>
    obtain ⟨e, he, rfl⟩ := hm
    have ht' : t ∈ (wrapMD e).toMethod.subtasks.T := ht
    exact .method ⟨wrapMD e, List.mem_append_left _ (List.mem_map_of_mem he), rfl⟩ ih ht'
      (by rw [wrapMD_label hp he ht', hc]; rfl)

/-! ## Total order -/

theorem weak_isTO_tnI_iff : (weakDesc p).toProblem.IsTO_tnI ↔ p.toProblem.toArt.IsTO_tnI :=
  Iff.rfl

theorem leaf_isTO (y : FActDesc) (j : ℕ) :
    (MethodDesc.toMethod (2 * y.1 + 1, ([0], [], [(0, false, Nat.pair y.1 j)]))).subtasks.IsTotallyOrdered := by
  intro t ht t' ht' hne
  simp [MethodDesc.toMethod, TnDesc.toTaskNetwork, TnDesc.ids] at ht ht'
  exact absurd (ht.trans ht'.symm) hne

theorem weak_isTO_M_iff (hp : p.Valid) :
    (weakDesc p).toProblem.IsTO_M ↔ p.toProblem.toArt.IsTO_M := by
  constructor
  · rintro h m ⟨⟨e, he, rfl⟩, hr⟩
    exact h (wrapMD e).toMethod ⟨⟨wrapMD e, List.mem_append_left _ (List.mem_map_of_mem he), rfl⟩,
      reach_P₀ hp hr⟩
  · rintro h m' ⟨hm, hr⟩
    rcases mem_weakDesc_methods hm with ⟨e, he, rfl⟩ | ⟨y, -, j, -, rfl⟩
    · rcases reach_Q hp hr with ⟨c, hc, hrc⟩ | hodd
      · have hc' : e.1 = c := by simp [wrapMD, MethodDesc.toMethod] at hc; omega
        rw [← hc'] at hrc
        exact h e.toMethod ⟨⟨e, he, rfl⟩, hrc⟩
      · simp [wrapMD, MethodDesc.toMethod] at hodd <;> omega
    · exact leaf_isTO y j

theorem weak_isTO_iff (hp : p.Valid) :
    (weakDesc p).toProblem.IsTO ↔ p.toProblem.toArt.IsTO :=
  and_congr weak_isTO_tnI_iff (weak_isTO_M_iff hp)

/-! ## Acyclicity and tail recursion -/

/-- The stratification of the translation: wrapped primitive names (odd) below the original
compound names (even), ordered by `≤` among themselves. -/
def wLe (le : ℕ → ℕ → Prop) (x y : ℕ) : Prop :=
  if x % 2 = 1 then (y % 2 = 1 → x ≤ y) else (y % 2 = 0 ∧ le (x / 2) (y / 2))

theorem wLe_even {le : ℕ → ℕ → Prop} (c d : ℕ) : wLe le (2 * c) (2 * d) ↔ le c d := by
  simp [wLe]

theorem wLe_odd_even {le : ℕ → ℕ → Prop} {x : ℕ} (hx : x % 2 = 1) (d : ℕ) :
    wLe le x (2 * d) ∧ ¬ wLe le (2 * d) x := by
  simp [wLe, hx]

theorem strat_of (hp : p.Valid) {le : ℕ → ℕ → Prop} (hs : (PP p).IsStratification le) :
    (QP p).IsStratification (wLe le) where
  refl x hx := by
    rcases reach_Q hp hx with ⟨c, rfl, hc⟩ | hodd
    · exact (wLe_even c c).2 (hs.refl c hc)
    · simp [wLe, hodd]
  trans x y z hx hy hz hxy hyz := by
    rcases reach_Q hp hx with ⟨c, rfl, hc⟩ | hx'
    · rcases reach_Q hp hy with ⟨d, rfl, hd⟩ | hy'
      · rcases reach_Q hp hz with ⟨f, rfl, hf⟩ | hz'
        · exact (wLe_even c f).2 (hs.trans c d f hc hd hf ((wLe_even c d).1 hxy) ((wLe_even d f).1 hyz))
        · exact absurd hyz (wLe_odd_even hz' d).2
      · exact absurd hxy (wLe_odd_even hy' c).2
    · simp only [wLe, hx', if_true] at hxy ⊢
      intro hz'
      rcases Nat.mod_two_eq_zero_or_one y with hy' | hy'
      · simp [wLe, hy', hz'] at hyz
      · have := hxy hy'; simp [wLe, hy', hz'] at hyz <;> omega
  total x y hx hy := by
    rcases reach_Q hp hx with ⟨c, rfl, hc⟩ | hx'
    · rcases reach_Q hp hy with ⟨d, rfl, hd⟩ | hy'
      · rcases hs.total c d hc hd with h | h
        · exact Or.inl ((wLe_even c d).2 h)
        · exact Or.inr ((wLe_even d c).2 h)
      · exact Or.inr (wLe_odd_even hy' c).1
    · rcases reach_Q hp hy with ⟨d, rfl, hd⟩ | hy'
      · exact Or.inl (wLe_odd_even hx' d).1
      · simp only [wLe, hx', hy', if_true, forall_const]; omega

theorem strat_back (hp : p.Valid) {le : ℕ → ℕ → Prop} (hs : (QP p).IsStratification le) :
    (PP p).IsStratification (fun c d => le (2 * c) (2 * d)) where
  refl c hc := hs.refl _ (reach_P₀ hp hc)
  trans a b c ha hb hc := hs.trans _ _ _ (reach_P₀ hp ha) (reach_P₀ hp hb) (reach_P₀ hp hc)
  total a b ha hb := hs.total _ _ (reach_P₀ hp ha) (reach_P₀ hp hb)

theorem weak_isACYC_iff (hp : p.Valid) :
    (weakDesc p).toProblem.IsACYC ↔ p.toProblem.toArt.IsACYC := by
  constructor
  · rintro ⟨le, hs⟩
    refine ⟨fun c d => le (2 * c) (2 * d), strat_back hp hs.strat, ?_, ?_⟩
    · intro a b ha hb hab hba
      have := hs.antisymm _ _ (reach_P₀ hp ha) (reach_P₀ hp hb) hab hba
      omega
    · rintro m ⟨⟨e, he, rfl⟩, hr⟩ t ht c hc
      have ht' : t ∈ (wrapMD e).toMethod.subtasks.T := ht
      exact hs.decreasing (wrapMD e).toMethod
        ⟨⟨wrapMD e, List.mem_append_left _ (List.mem_map_of_mem he), rfl⟩, reach_P₀ hp hr⟩ t ht' _
        (by rw [wrapMD_label hp he ht', hc]; rfl)
  · rintro ⟨le, hs⟩
    refine ⟨wLe le, strat_of hp hs.strat, ?_, ?_⟩
    · intro x y hx hy hxy hyx
      rcases reach_Q hp hx with ⟨c, rfl, hc⟩ | hx'
      · rcases reach_Q hp hy with ⟨d, rfl, hd⟩ | hy'
        · rw [hs.antisymm c d hc hd ((wLe_even c d).1 hxy) ((wLe_even d c).1 hyx)]
        · exact absurd hxy (wLe_odd_even hy' c).2
      · rcases reach_Q hp hy with ⟨d, rfl, hd⟩ | hy'
        · exact absurd hyx (wLe_odd_even hx' d).2
        · simp only [wLe, hx', hy', if_true, forall_const] at hxy hyx; omega
    · rintro m' ⟨hm, hr⟩ t ht x hx
      rcases mem_weakDesc_methods hm with ⟨e, he, rfl⟩ | ⟨y, -, j, -, rfl⟩
      · rcases reach_Q hp hr with ⟨c, hc, hrc⟩ | hodd
        · have hc' : e.1 = c := by simp [wrapMD, MethodDesc.toMethod] at hc; omega
          rw [hc]
          rw [wrapMD_label hp he ht] at hx
          rw [← hc'] at hrc
          rcases wE_inr hx with ⟨d, hd, rfl⟩ | ⟨a, -, rfl⟩
          · have := hs.decreasing e.toMethod ⟨⟨e, he, rfl⟩, hrc⟩ t ht d hd
            replace this : le d c ∧ ¬ le c d := by rw [← hc']; exact this
            exact ⟨(wLe_even d c).2 this.1, fun h => this.2 ((wLe_even c d).1 h)⟩
          · exact wLe_odd_even (by omega) c
        · simp [wrapMD, MethodDesc.toMethod] at hodd <;> omega
      · rw [leaf_label] at hx; cases hx

theorem isLastId_wrapMD (e : MethodDesc) (t : ℕ) :
    (wrapMD e).toMethod.subtasks.IsLastId t ↔ e.toMethod.subtasks.IsLastId t := Iff.rfl

theorem weak_isTailREC_iff (hp : p.Valid) :
    (weakDesc p).toProblem.IsTailREC ↔ p.toProblem.toArt.IsTailREC := by
  constructor
  · rintro ⟨le, hs⟩
    refine ⟨fun c d => le (2 * c) (2 * d), strat_back hp hs.strat, ?_, ?_⟩
    · rintro m ⟨⟨e, he, rfl⟩, hr⟩ t ht hl c hc
      have ht' : t ∈ (wrapMD e).toMethod.subtasks.T := ht
      exact hs.last (wrapMD e).toMethod
        ⟨⟨wrapMD e, List.mem_append_left _ (List.mem_map_of_mem he), rfl⟩, reach_P₀ hp hr⟩ t ht'
        hl _ (by rw [wrapMD_label hp he ht', hc]; rfl)
    · rintro m ⟨⟨e, he, rfl⟩, hr⟩ t ht hl c hc
      have ht' : t ∈ (wrapMD e).toMethod.subtasks.T := ht
      exact hs.nonlast (wrapMD e).toMethod
        ⟨⟨wrapMD e, List.mem_append_left _ (List.mem_map_of_mem he), rfl⟩, reach_P₀ hp hr⟩ t ht'
        hl _ (by rw [wrapMD_label hp he ht', hc]; rfl)
  · rintro ⟨le, hs⟩
    have key : ∀ m', (QP p).ReachableMethod m' → ∀ t ∈ m'.subtasks.T, ∀ x,
        m'.subtasks.α t = Sum.inr x → ∃ e ∈ p.methods, m' = (wrapMD e).toMethod ∧
          (PP p).ReachableMethod e.toMethod ∧
          ((∃ d, e.toMethod.subtasks.α t = Sum.inr d ∧ x = 2 * d) ∨ x % 2 = 1) := by
      rintro m' ⟨hm, hr⟩ t ht x hx
      rcases mem_weakDesc_methods hm with ⟨e, he, rfl⟩ | ⟨y, -, j, -, rfl⟩
      · rcases reach_Q hp hr with ⟨c, hc, hrc⟩ | hodd
        · have hc' : e.1 = c := by simp [wrapMD, MethodDesc.toMethod] at hc; omega
          rw [← hc'] at hrc
          refine ⟨e, he, rfl, ⟨⟨e, he, rfl⟩, hrc⟩, ?_⟩
          rw [wrapMD_label hp he ht] at hx
          rcases wE_inr hx with ⟨d, hd, rfl⟩ | ⟨a, -, rfl⟩
          · exact Or.inl ⟨d, hd, rfl⟩
          · right; omega
        · simp [wrapMD, MethodDesc.toMethod] at hodd <;> omega
      · rw [leaf_label] at hx; cases hx
    refine ⟨wLe le, strat_of hp hs.strat, ?_, ?_⟩
    · intro m' hr t ht hl x hx
      obtain ⟨e, he, rfl, hre, hd | hodd⟩ := key m' hr t ht x hx
      · obtain ⟨d, hd, rfl⟩ := hd
        show wLe le (2 * d) (2 * e.1)
        exact (wLe_even d e.1).2 (hs.last e.toMethod hre t ht hl d hd)
      · exact (wLe_odd_even hodd e.1).1
    · intro m' hr t ht hl x hx
      obtain ⟨e, he, rfl, hre, hd | hodd⟩ := key m' hr t ht x hx
      · obtain ⟨d, hd, rfl⟩ := hd
        have := hs.nonlast e.toMethod hre t ht hl d hd
        exact ⟨(wLe_even d e.1).2 this.1, fun h => this.2 ((wLe_even e.1 d).1 h)⟩
      · exact wLe_odd_even hodd e.1

end FOND
