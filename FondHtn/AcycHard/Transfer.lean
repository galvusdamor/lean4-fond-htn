import FondHtn.AcycHard.ChainGame
import FondHtn.Lang.Desc
/-!
# Transfer of the chain game to encoded actions

**`FOND.AcycHard.cwin_transfer`**: the chain game with a control `u ++ refill^R` (`u` without
`refill`) is invariant under an injective encoding of the facts and an injective naming of the
pool actions, provided the encoded actions are the images of the original ones — except
`refill`, of which both sides only need that the *trash phase* (the refills and the remaining
pool tasks) is won whenever there are at least as many refills as remaining pool tasks.
-/

namespace FOND

namespace AcycHard

open HTN

variable {F₁ F₂ : Type} (fe : F₁ → F₂)

/-- The image of an action under a fact encoding. -/
def encAct (a : Action F₁) : Action F₂ :=
  ⟨fe '' a.pre, fe '' a.preNeg, (fun e => (fe '' e.1, fe '' e.2)) '' a.effs⟩

variable {fe}

theorem encAct_applicable (hinj : Function.Injective fe) (a : Action F₁) (s : Set F₁) :
    (encAct fe a).Applicable (fe '' s) ↔ a.Applicable s := by
  simp only [Action.Applicable, encAct, Set.image_subset_image_iff hinj,
    Set.disjoint_image_iff hinj]

theorem encAct_outcomes (hinj : Function.Injective fe) (a : Action F₁) (s : Set F₁) (s₂ : Set F₂) :
    s₂ ∈ (encAct fe a).outcomes (fe '' s) ↔ ∃ s₁ ∈ a.outcomes s, s₂ = fe '' s₁ := by
  simp only [Action.mem_outcomes, encAct, Set.mem_image, Action.applyEff]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, by rw [Set.image_union, Set.image_diff hinj]⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, by rw [Set.image_union, Set.image_diff hinj]⟩

variable {CA PA CA₂ PA₂ : Type} [DecidableEq PA] [DecidableEq PA₂]
  {δC₁ : CA → Action F₁} {δP₁ : PA → Action F₁} {δC₂ : CA₂ → Action F₂} {δP₂ : PA₂ → Action F₂}
  {nC : CA → CA₂} {nP : PA → PA₂} {refill : CA} {R : ℕ} {AP : PA → Prop}

theorem map_erase_inj (hnP : Function.Injective nP) (M : Multiset (List PA)) (c : List PA) :
    (M.map (List.map nP)).erase (c.map nP) = (M.erase c).map (List.map nP) :=
  (Multiset.map_erase _ (List.map_injective_iff.2 hnP) _ _).symm

theorem size_erase_lt {M : Multiset (List PA)} {a : PA} {c : List PA} (h : a :: c ∈ M) :
    WSys.size (c ::ₘ M.erase (a :: c)) < WSys.size M := by
  have := WSys.size_step h
  omega

/-- The hypotheses of the transfer. -/
structure TransferHyp (fe : F₁ → F₂) (δC₁ : CA → Action F₁) (δP₁ : PA → Action F₁)
    (δC₂ : CA₂ → Action F₂) (δP₂ : PA₂ → Action F₂) (nC : CA → CA₂) (nP : PA → PA₂) (refill : CA)
    (R : ℕ) (AP : PA → Prop) : Prop where
  inj : Function.Injective fe
  injP : Function.Injective nP
  ctl : ∀ x, x ≠ refill → δC₂ (nC x) = encAct fe (δC₁ x)
  pool : ∀ x, AP x → δP₂ (nP x) = encAct fe (δP₁ x)
  trash₁ : ∀ M s, (∀ c ∈ M, ∀ a ∈ c, AP a) → WSys.size M ≤ R →
    CWin δC₁ δP₁ (List.replicate R refill) M s
  trash₂ : ∀ M s, (∀ c ∈ M, ∀ a ∈ c, AP a) → WSys.size M ≤ R →
    CWin δC₂ δP₂ (List.replicate R (nC refill)) (M.map (List.map nP)) s

theorem AP_step {M : Multiset (List PA)} (hM : ∀ c ∈ M, ∀ a ∈ c, AP a) {a : PA} {c : List PA}
    (h : a :: c ∈ M) : ∀ c' ∈ c ::ₘ M.erase (a :: c), ∀ x ∈ c', AP x := by
  intro c' hc' x hx
  rcases Multiset.mem_cons.1 hc' with rfl | hc'
  · exact hM _ h x (List.mem_cons_of_mem _ hx)
  · exact hM c' (Multiset.mem_of_mem_erase hc') x hx

theorem cwin_transfer_mp (hT : TransferHyp fe δC₁ δP₁ δC₂ δP₂ nC nP refill R AP) :
    ∀ {ctl : List CA} {M : Multiset (List PA)} {s : Set F₁}, CWin δC₁ δP₁ ctl M s →
      ∀ u, refill ∉ u → ctl = u ++ List.replicate R refill → (∀ c ∈ M, ∀ a ∈ c, AP a) →
        WSys.size M ≤ R → CWin δC₂ δP₂ ((u ++ List.replicate R refill).map nC)
          (M.map (List.map nP)) (fe '' s) := by
  intro ctl M s h
  induction h with
  | @done M s hM =>
    intro u hu hc hAP hR
    have hu0 : u = [] := by
      cases u with
      | nil => rfl
      | cons x u => simp at hc
    subst hu0
    simpa using hT.trash₂ M _ hAP hR
  | @ctl a ctl' M s happ hall ih =>
    intro u hu hc hAP hR
    cases u with
    | nil => simpa using hT.trash₂ M _ hAP hR
    | cons x u =>
      simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hx : a ≠ refill := fun e => hu (by simp [e])
      simp only [List.cons_append, List.map_cons]
      refine .ctl (by rw [hT.ctl a hx, encAct_applicable hT.inj]; exact happ) fun s₂ hs₂ => ?_
      rw [hT.ctl a hx, encAct_outcomes hT.inj] at hs₂
      obtain ⟨s₁, hs₁, rfl⟩ := hs₂
      exact ih s₁ hs₁ u (fun h => hu (List.mem_cons_of_mem _ h)) rfl hAP hR
  | @pool ctl M s a c hc happ hall ih =>
    intro u hu hctl hAP hR
    cases u with
    | nil => simpa using hT.trash₂ M _ hAP hR
    | cons x u =>
      have ha := hAP _ hc a (by simp)
      have hc' : nP a :: c.map nP ∈ M.map (List.map nP) := Multiset.mem_map.2 ⟨_, hc, rfl⟩
      refine .pool hc' (by rw [hT.pool a ha, encAct_applicable hT.inj]; exact happ) fun s₂ hs₂ => ?_
      rw [hT.pool a ha, encAct_outcomes hT.inj] at hs₂
      obtain ⟨s₁, hs₁, rfl⟩ := hs₂
      have := ih s₁ hs₁ (x :: u) hu hctl (AP_step hAP hc)
        (by have := size_erase_lt hc; omega)
      rwa [Multiset.map_cons, ← map_erase_inj hT.injP] at this

theorem cwin_transfer_mpr (hT : TransferHyp fe δC₁ δP₁ δC₂ δP₂ nC nP refill R AP) :
    ∀ {ctl₂ : List CA₂} {M₂ : Multiset (List PA₂)} {s₂ : Set F₂}, CWin δC₂ δP₂ ctl₂ M₂ s₂ →
      ∀ u M s, refill ∉ u → ctl₂ = (u ++ List.replicate R refill).map nC →
        M₂ = M.map (List.map nP) → s₂ = fe '' s → (∀ c ∈ M, ∀ a ∈ c, AP a) →
        WSys.size M ≤ R → CWin δC₁ δP₁ (u ++ List.replicate R refill) M s := by
  intro ctl₂ M₂ s₂ h
  induction h with
  | @done M₂ s₂ hM =>
    intro u M s hu hc hM₂ hs hAP hR
    have hu0 : u = [] := by
      cases u with
      | nil => rfl
      | cons x u => simp at hc
    subst hu0
    simpa using hT.trash₁ M s hAP hR
  | @ctl a ctl' M₂ s₂ happ hall ih =>
    intro u M s hu hc hM₂ hs hAP hR
    subst hM₂ hs
    cases u with
    | nil => simpa using hT.trash₁ M s hAP hR
    | cons x u =>
      simp only [List.cons_append, List.map_cons, List.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hx : x ≠ refill := fun e => hu (by simp [e])
      rw [hT.ctl x hx, encAct_applicable hT.inj] at happ
      refine .ctl happ fun s₁ hs₁ => ?_
      refine ih (fe '' s₁) ?_ u M s₁ (fun h => hu (List.mem_cons_of_mem _ h)) (by simp) rfl rfl hAP hR
      rw [hT.ctl x hx, encAct_outcomes hT.inj]; exact ⟨s₁, hs₁, rfl⟩
  | @pool ctl₂ M₂ s₂ a₂ c₂ hc happ hall ih =>
    intro u M s hu hctl hM₂ hs hAP hR
    subst hM₂ hs
    cases u with
    | nil => simpa using hT.trash₁ M s hAP hR
    | cons x u =>
      obtain ⟨ch, hch, he⟩ := Multiset.mem_map.1 hc
      obtain ⟨a, c, rfl⟩ : ∃ a c, ch = a :: c := by
        cases ch with
        | nil => simp at he
        | cons a c => exact ⟨a, c, rfl⟩
      simp only [List.map_cons, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have ha := hAP _ hch a (by simp)
      rw [hT.pool a ha, encAct_applicable hT.inj] at happ
      refine .pool hch happ fun s₁ hs₁ => ?_
      refine ih (fe '' s₁) ?_ (x :: u) _ s₁ hu hctl ?_ rfl (AP_step hAP hch)
        (by have := size_erase_lt hch; omega)
      · rw [hT.pool a ha, encAct_outcomes hT.inj]; exact ⟨s₁, hs₁, rfl⟩
      · rw [Multiset.map_cons, ← map_erase_inj hT.injP]; rfl

/-- **The transfer of the chain game.** -/
theorem cwin_transfer (hT : TransferHyp fe δC₁ δP₁ δC₂ δP₂ nC nP refill R AP) {u : List CA}
    (hu : refill ∉ u) {M : Multiset (List PA)} (hAP : ∀ c ∈ M, ∀ a ∈ c, AP a)
    (hR : WSys.size M ≤ R) (s : Set F₁) :
    CWin δC₂ δP₂ ((u ++ List.replicate R refill).map nC) (M.map (List.map nP)) (fe '' s) ↔
      CWin δC₁ δP₁ (u ++ List.replicate R refill) M s :=
  ⟨fun h => cwin_transfer_mpr hT h u M s hu rfl rfl rfl hAP hR,
    fun h => cwin_transfer_mp hT h u hu rfl hAP hR⟩

/-! ## The trash phase on a finite fact set -/

/-- **The trash phase**: a refill makes every pool action of the pool applicable. -/
theorem cwin_trash {F CA PA : Type} [DecidableEq PA] {δC : CA → Action F} {δP : PA → Action F}
    {rf : CA} {full : Set F} {AP : PA → Prop}
    (hrf : ∀ s, (δC rf).Applicable s ∧ ∀ s' ∈ (δC rf).outcomes s, full ⊆ s')
    (hP : ∀ a, AP a → ∀ s, full ⊆ s → (δP a).Applicable s) :
    ∀ (R : ℕ) (M : Multiset (List PA)) (s : Set F), (∀ c ∈ M, ∀ a ∈ c, AP a) → WSys.size M ≤ R →
      CWin δC δP (List.replicate R rf) M s := by
  intro R
  induction R with
  | zero =>
    intro M s _ h
    exact CWin.done (WSys.size_eq_zero (Nat.le_zero.1 h))
  | succ R ih =>
    intro M s hAP h
    refine CWin.ctl (hrf s).1 fun s' hs' => ?_
    by_cases h0 : WSys.size M = 0
    · exact ih M s' hAP (by omega)
    · have : ∃ c ∈ M, c ≠ [] := by
        by_contra hc
        push_neg at hc
        apply h0
        simp only [WSys.size]
        rw [Multiset.sum_eq_zero_iff]
        intro n hn
        obtain ⟨c, hc', rfl⟩ := Multiset.mem_map.1 hn
        simp [hc c hc']
      obtain ⟨c, hc, hne⟩ := this
      obtain ⟨a, c', rfl⟩ := List.exists_cons_of_ne_nil hne
      have hs := WSys.size_step hc
      exact CWin.pool hc (hP a (hAP _ hc a (by simp)) s' ((hrf s).2 s' hs'))
        (fun s'' _ => ih _ s'' (AP_step hAP hc) (by omega))

/-! ## Described actions as encoded actions -/

/-- The action of lists of facts. -/
def listAct {F : Type} (pre neg : List F) (effs : List (List F × List F)) : Action F :=
  ⟨{f | f ∈ pre}, {f | f ∈ neg}, {e | ∃ x ∈ effs, e = ({f | f ∈ x.1}, {f | f ∈ x.2})}⟩

theorem toAction_enc {F : Type} (fe : F → ℕ) (nm : ℕ) (pre neg : List F) (effs : List (List F × List F)) :
    FActDesc.toAction (nm, pre.map fe, neg.map fe, effs.map fun x => (x.1.map fe, x.2.map fe)) =
      encAct fe (listAct pre neg effs) := by
  simp only [FActDesc.toAction, encAct, listAct, FActDesc.effs]
  congr 1
  · ext f; simp
  · ext f; simp
  · ext e
    simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, by ext <;> simp⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, by ext <;> simp⟩

end AcycHard

end FOND
