import FondHtn.FairSigma.UGame
/-!
# The unbounded fair game in Kleene normal form

The unbounded fair game `FOND.FS.UWin` quantifies over a set `X` and (inductively) over
attractor derivations.  Both are replaced by a pair of functions on configurations: membership
`xf` in `X` and a rank `af` (`0`: not in the attractor; `r + 1`: in the attractor with rank `r`),
subject to a *local* condition `FOND.FS.Loc` at every configuration
(**`FOND.FS.uWin_iff_loc`**).

Encoding configurations by numbers (`code`, with a left inverse `dec`), the pair of functions is
one function `f : ℕ → ℕ` (`f (code c) = 2 · af c + [xf c]`), and the local conditions are checked
on finite prefixes of `f` (`FOND.FS.chk`): **`FOND.FS.exists_chk_iff`**.
-/

namespace FOND

namespace FS

section Rank

variable {α σ : Type} (acc uni : α × σ → Bool) (step : α × σ × σ → Bool) (a : α)

/-- The attractor with heights. -/
inductive UAttrH (X : σ → Prop) : ℕ → σ → Prop
  | acc {n : ℕ} {c : σ} : acc (a, c) = true → UAttrH X n c
  | ex {n : ℕ} {c c' : σ} : uni (a, c) = false → step (a, c, c') = true → X c' →
      UAttrH X n c' → UAttrH X (n + 1) c
  | univ {n : ℕ} {c c' : σ} : uni (a, c) = true → (∀ c'', step (a, c, c'') = true → X c'') →
      step (a, c, c') = true → UAttrH X n c' → UAttrH X (n + 1) c

/-- **The local condition** at a configuration. -/
def Loc (xf : σ → Prop) (af : σ → ℕ) (c : σ) : Prop :=
  (xf c → af c ≠ 0) ∧ ∀ r, af c = r + 1 →
    (acc (a, c) = true ∨
      (uni (a, c) = false ∧ ∃ c', step (a, c, c') = true ∧ xf c' ∧ 0 < af c' ∧ af c' ≤ r) ∨
      (uni (a, c) = true ∧ (∀ c'', step (a, c, c'') = true → xf c'') ∧
        ∃ c', step (a, c, c') = true ∧ 0 < af c' ∧ af c' ≤ r))

variable {acc uni step a}

theorem uAttrH_of_uAttr {X : σ → Prop} {c : σ} (h : UAttr acc uni step a X c) :
    ∃ n, UAttrH acc uni step a X n c := by
  induction h with
  | acc h => exact ⟨0, .acc h⟩
  | ex hu hs hX _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .ex hu hs hX hn⟩
  | univ hu hall hs _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .univ hu hall hs hn⟩

/-- **The fair game as local conditions on a pair of functions.** -/
theorem uWin_iff_loc {c₀ : σ} :
    UWin acc uni step a c₀ ↔ ∃ (xf : σ → Prop) (af : σ → ℕ), xf c₀ ∧ ∀ c, Loc acc uni step a xf af c := by
  classical
  constructor
  · rintro ⟨X, hX₀, hXa⟩
    let af : σ → ℕ := fun c => if h : ∃ n, UAttrH acc uni step a X n c then Nat.find h + 1 else 0
    have haf : ∀ c n, UAttrH acc uni step a X n c → 0 < af c ∧ af c ≤ n + 1 := by
      intro c n hn
      have h : ∃ n, UAttrH acc uni step a X n c := ⟨n, hn⟩
      simp only [af, dif_pos h]
      exact ⟨by omega, by have := Nat.find_min' h hn; omega⟩
    refine ⟨X, af, hX₀, fun c => ⟨fun hX => ?_, fun r hr => ?_⟩⟩
    · obtain ⟨n, hn⟩ := uAttrH_of_uAttr (hXa c hX)
      exact (Nat.pos_iff_ne_zero.1 (haf c n hn).1)
    · have h : ∃ n, UAttrH acc uni step a X n c := by
        by_contra h; simp only [af, dif_neg h] at hr; omega
      have hr' : Nat.find h = r := by simp only [af, dif_pos h] at hr; omega
      have hs := Nat.find_spec h
      rw [hr'] at hs
      cases hs with
      | acc h => exact Or.inl h
      | @ex n _ c' hu hst hX hn =>
        exact Or.inr (Or.inl ⟨hu, c', hst, hX, (haf c' n hn).1, (haf c' n hn).2⟩)
      | @univ n _ c' hu hall hst hn =>
        exact Or.inr (Or.inr ⟨hu, hall, c', hst, (haf c' n hn).1, (haf c' n hn).2⟩)
  · rintro ⟨xf, af, hx₀, hloc⟩
    have key : ∀ r c, af c = r + 1 → UAttr acc uni step a xf c := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro c hc
        rcases (hloc c).2 r hc with h | ⟨hu, c', hs, hx, h0, hle⟩ | ⟨hu, hall, c', hs, h0, hle⟩
        · exact .acc h
        · exact .ex hu hs hx (ih (af c' - 1) (by omega) c' (by omega))
        · exact .univ hu hall hs (ih (af c' - 1) (by omega) c' (by omega))
    refine ⟨xf, hx₀, fun c hc => key (af c - 1) c ?_⟩
    have := (hloc c).1 hc
    omega

end Rank

section Check

variable {α σ : Type} (acc uni : α × σ → Bool) (a : α) (S : σ → List σ) (code : ℕ → ℕ)

/-- The value of a configuration, looked up in a prefix. -/
def look (code : σ → ℕ) (l : List ℕ) (c : σ) : ℕ := l.getI (code c)

/-- The local condition, as a Boolean function of a prefix. -/
def locB (code : σ → ℕ) (l : List ℕ) (c : σ) : Bool :=
  (look code l c % 2 != 1 || look code l c / 2 != 0) &&
    (look code l c / 2 == 0 || acc (a, c) ||
      (!uni (a, c) && (S c).any fun c' =>
        look code l c' % 2 == 1 && decide (0 < look code l c' / 2) &&
          decide (look code l c' / 2 ≤ look code l c / 2 - 1)) ||
      (uni (a, c) && (S c).all (fun c' => look code l c' % 2 == 1) && (S c).any fun c' =>
        decide (0 < look code l c' / 2) && decide (look code l c' / 2 ≤ look code l c / 2 - 1)))

/-- **The check of a prefix**: the initial configuration is in `X`, and the local condition
holds at every configuration whose code and successor codes are inside the prefix. -/
def chk (code : σ → ℕ) (dec : ℕ → σ) (c₀ : σ) (l : List ℕ) : Bool :=
  (!decide (code c₀ < l.length) || look code l c₀ % 2 == 1) &&
    (List.range l.length).all fun k =>
      !(decide (code (dec k) = k) && (S (dec k)).all fun c' => decide (code c' < l.length)) ||
        locB acc uni a S code l (dec k)

variable {acc uni a S}

theorem getI_map_range {f : ℕ → ℕ} {n k : ℕ} (hk : k < n) : ((List.range n).map f).getI k = f k := by
  rw [List.getI_eq_getElem _ (by simpa using hk)]; simp

theorem le_foldr_max_base (L : List ℕ) (b : ℕ) : b ≤ L.foldr max b := by
  induction L with
  | nil => simp
  | cons x xs ih => simp only [List.foldr_cons]; exact le_trans ih (le_max_right _ _)

theorem le_foldr_max {L : List ℕ} {x : ℕ} (b : ℕ) (h : x ∈ L) : x ≤ L.foldr max b := by
  induction L with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- **Prefix checks are the local conditions.** -/
theorem exists_chk_iff (step : α × σ × σ → Bool) (hS : ∀ c c', step (a, c, c') = true ↔ c' ∈ S c)
    (code : σ → ℕ) (dec : ℕ → σ) (hdc : ∀ c, dec (code c) = c) (c₀ : σ) :
    (∃ f : ℕ → ℕ, ∀ n, chk acc uni a S code dec c₀ ((List.range n).map f) = true) ↔
      ∃ (xf : σ → Prop) (af : σ → ℕ), xf c₀ ∧ ∀ c, Loc acc uni step a xf af c := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun c => f (code c) % 2 = 1, fun c => f (code c) / 2, ?_, fun c => ?_⟩
    · have h := hf (code c₀ + 1)
      simp only [chk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        List.length_map, List.length_range, beq_iff_eq] at h
      rcases h.1 with h | h
      · omega
      · rwa [look, getI_map_range (by omega)] at h
    · set N := ((S c).map code).foldr max (code c) + 1 with hN
      have hle : ∀ c' ∈ S c, code c' < N := fun c' hc' => by
        have := le_foldr_max (L := (S c).map code) (code c) (List.mem_map.2 ⟨c', hc', rfl⟩); omega
      have hcN : code c < N := by have := le_foldr_max_base ((S c).map code) (code c); omega
      have h := hf N
      simp only [chk, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.length_map,
        List.length_range] at h
      have hk := h.2 (code c) hcN
      rw [hdc] at hk
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
        List.all_eq_false, decide_eq_true_eq] at hk
      have hlook : ∀ c', code c' < N → look code ((List.range N).map f) c' = f (code c') :=
        fun c' h => getI_map_range h
      rcases hk with (hk | ⟨c', hc', hk⟩) | hk
      · exact absurd trivial hk
      · exact absurd (hle c' hc') hk
      simp only [locB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
        Bool.not_eq_true', List.any_eq_true, List.all_eq_true, decide_eq_true_eq,
        hlook c hcN] at hk
      obtain ⟨h1, h2⟩ := hk
      refine ⟨fun hx => by rcases h1 with h1 | h1 <;> omega, fun r hr => ?_⟩
      beta_reduce at hr ⊢
      rcases h2 with ((h2 | h2) | ⟨hu, c', hc', ⟨hx', h0⟩, hle'⟩) | ⟨⟨hu, hall⟩, c', hc', h0, hle'⟩
      · omega
      · exact Or.inl h2
      · rw [hlook c' (hle c' hc')] at hx' h0 hle'
        exact Or.inr (Or.inl ⟨hu, c', (hS c c').2 hc', hx', h0, by omega⟩)
      · rw [hlook c' (hle c' hc')] at h0 hle'
        refine Or.inr (Or.inr ⟨hu, fun c'' hs'' => ?_, c', (hS c c').2 hc', h0, by omega⟩)
        have hc'' := (hS c c'').1 hs''
        have := hall c'' hc''
        rwa [hlook c'' (hle c'' hc'')] at this
  · rintro ⟨xf, af, hx₀, hloc⟩
    let f : ℕ → ℕ := fun k => if code (dec k) = k then 2 * af (dec k) + (if xf (dec k) then 1 else 0) else 0
    have hf : ∀ c, f (code c) = 2 * af c + (if xf c then 1 else 0) := by
      intro c; simp only [f, hdc, if_true]
    have hmod : ∀ c, (f (code c) % 2 = 1 ↔ xf c) := by
      intro c; rw [hf]; split_ifs with h <;> simp [h]
    have hdiv : ∀ c, f (code c) / 2 = af c := by
      intro c; rw [hf]; split_ifs <;> omega
    refine ⟨f, fun n => ?_⟩
    have hlook : ∀ c', code c' < n → look code ((List.range n).map f) c' = f (code c') :=
      fun c' h => getI_map_range h
    simp only [chk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      List.length_map, List.length_range, beq_iff_eq, List.all_eq_true, List.mem_range]
    refine ⟨?_, fun k hk => ?_⟩
    · by_cases h : code c₀ < n
      · right; rw [hlook c₀ h]; exact (hmod c₀).2 hx₀
      · left; exact h
    by_cases hc : code (dec k) = k ∧ ∀ c' ∈ S (dec k), code c' < n
    · right
      obtain ⟨hck, hcs⟩ := hc
      set c := dec k
      have hcn : code c < n := by rw [hck]; exact hk
      obtain ⟨h1, h2⟩ := hloc c
      simp only [locB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
        Bool.not_eq_true', List.any_eq_true, List.all_eq_true, decide_eq_true_eq, hlook c hcn,
        hdiv]
      refine ⟨?_, ?_⟩
      · by_cases hx : xf c
        · right; exact h1 hx
        · left; rwa [hmod]
      · by_cases h0 : af c = 0
        · left; left; left; exact h0
        rcases h2 (af c - 1) (by omega) with h | ⟨hu, c', hs, hx, h0', hle⟩ | ⟨hu, hall, c', hs, h0', hle⟩
        · left; left; right; exact h
        · left; right
          have hc' := (hS c c').1 hs
          refine ⟨hu, c', hc', ⟨?_, ?_⟩, ?_⟩ <;> rw [hlook c' (hcs c' hc')]
          · exact (hmod c').2 hx
          · rw [hdiv]; exact h0'
          · rw [hdiv]; exact hle
        · right
          refine ⟨⟨hu, fun c'' hc'' => ?_⟩, c', (hS c c').1 hs, ?_, ?_⟩
          · rw [hlook c'' (hcs c'' hc'')]; exact (hmod c'').2 (hall c'' ((hS c c'').2 hc''))
          · rw [hlook c' (hcs c' ((hS c c').1 hs)), hdiv]; exact h0'
          · rw [hlook c' (hcs c' ((hS c c').1 hs)), hdiv]; exact hle
    · left
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, List.all_eq_false,
        decide_eq_true_eq]
      by_cases h1 : code (dec k) = k
      · right; push_neg at hc; obtain ⟨c', hc', h⟩ := hc h1; exact ⟨c', hc', by omega⟩
      · left; exact h1

end Check

end FS

end FOND
