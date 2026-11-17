import FondHtn.DB25.Ops
/-!
# Correctness of the register gadgets

`FOND.DB.phasesWin_op`: for a well-formed operation `op` on the registers `V`,
`phasesWin (opPhases op) K (enc V ρ q) ↔ opSem op (fun ρ q => K (enc V ρ q)) ρ q`.
-/

namespace FOND

namespace DB

open Problem

theorem map_eraseIdx {α β : Type} (f : α → β) : ∀ (l : List α) (i : ℕ),
    (l.map f).eraseIdx i = (l.eraseIdx i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: l, i + 1 => by simp [map_eraseIdx f l i]

/-! ## Single-effect actions -/

theorem setWin_det (K : Set ℕ → Prop) (a : FActDesc) {e : List ℕ × List ℕ}
    (he : a.2.2.2 = [e]) (hn : a.2.2.1 = []) (s : Set ℕ) :
    setWin K [a.toAction] s ↔ (∀ f ∈ a.2.1, f ∈ s) ∧ K ((s \ {f | f ∈ e.2}) ∪ {f | f ∈ e.1}) := by
  rw [setWin_single, applicable_iff hn, outcomes_single he]
  simp

/-! ## Choice and nature -/

theorem enc_update {V : List ℕ} {ρ : ℕ → Bool} {q r : ℕ} (hr : r ∈ V) (b : Bool) :
    (enc V ρ q \ {f | f ∈ [lit r (!b)]}) ∪ {f | f ∈ [lit r b]} = enc V (Function.update ρ r b) q := by
  ext f
  simp only [enc, List.mem_singleton, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · rintro (⟨⟨v, hv, rfl⟩ | rfl, hne⟩ | rfl)
    · left
      refine ⟨v, hv, ?_⟩
      by_cases hvr : v = r
      · subst hvr
        rw [Function.update_self]
        cases b <;> cases h : ρ v <;> simp_all
      · rw [Function.update_of_ne hvr]
    · right; rfl
    · left; exact ⟨r, hr, by rw [Function.update_self]⟩
  · rintro (⟨v, hv, rfl⟩ | rfl)
    · by_cases hvr : v = r
      · subst hvr; right; rw [Function.update_self]
      · left
        rw [Function.update_of_ne hvr]
        exact ⟨Or.inl ⟨v, hv, rfl⟩, by simp [hvr]⟩
    · left; exact ⟨Or.inr rfl, by simp⟩

theorem phasesWin_choice {V : List ℕ} {r : ℕ} (hr : r ∈ V) (K : Set ℕ → Prop) (ρ : ℕ → Bool)
    (q : ℕ) : phasesWin (opPhases (.choice r)) K (enc V ρ q) ↔
      opSem (.choice r) (fun ρ q => K (enc V ρ q)) ρ q := by
  simp only [opPhases, phasesWin_cons, phasesWin_nil, List.map_cons, List.map_nil, opSem]
  rw [setWin_pair]
  have h0 : ∀ b (s : Set ℕ), (setA r b).toAction.Applicable s := fun b s => by
    rw [applicable_iff rfl]; simp [setA]
  have hout : ∀ b (s : Set ℕ), (setA r b).toAction.outcomes s =
      {(s \ {f | f ∈ [lit r (!b)]}) ∪ {f | f ∈ [lit r b]}} := fun b s =>
    outcomes_single (e := ([lit r b], [lit r (!b)])) rfl s
  simp only [h0, true_and, hout, Set.mem_singleton_iff, forall_eq, enc_update hr,
    Function.update_idem]
  constructor
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inr h
    · exact Or.inl h

theorem phasesWin_nature {V : List ℕ} {r : ℕ} (hr : r ∈ V) (K : Set ℕ → Prop) (ρ : ℕ → Bool)
    (q : ℕ) : phasesWin (opPhases (.nature r)) K (enc V ρ q) ↔
      opSem (.nature r) (fun ρ q => K (enc V ρ q)) ρ q := by
  simp only [opPhases, phasesWin_cons, phasesWin_nil, List.map_cons, List.map_nil, opSem]
  rw [setWin_single, applicable_iff rfl]
  simp only [natA, List.not_mem_nil, IsEmpty.forall_iff, implies_true, true_and]
  have hout : ∀ s', s' ∈ (natA r).toAction.outcomes (enc V ρ q) ↔
      ∃ b, s' = enc V (Function.update ρ r b) q := fun s' => by
    simp only [Action.outcomes, FActDesc.toAction, FActDesc.effs, natA, List.mem_cons,
      List.not_mem_nil, or_false, Set.mem_setOf_eq, Action.applyEff]
    constructor
    · rintro ⟨e, ⟨x, hx, rfl⟩, rfl⟩
      rcases hx with rfl | rfl
      · exact ⟨true, by rw [← enc_update hr true]; rfl⟩
      · exact ⟨false, by rw [← enc_update hr false]; rfl⟩
    · rintro ⟨b, rfl⟩
      cases b
      · exact ⟨_, ⟨_, Or.inr rfl, rfl⟩, by rw [← enc_update hr false]; rfl⟩
      · exact ⟨_, ⟨_, Or.inl rfl, rfl⟩, by rw [← enc_update hr true]; rfl⟩
  change (∀ s' ∈ (natA r).toAction.outcomes (enc V ρ q), K s') ↔ _
  simp only [hout]
  exact ⟨fun h b => h _ ⟨b, rfl⟩, fun h s' ⟨b, hb⟩ => hb ▸ h b⟩

/-! ## Copies -/

theorem copy_set {X : Set ℕ} {x1 x2 y1 y2 : ℕ} (h1 : x1 ∈ X) (h2 : x2 ∉ X) (h12 : y2 ≠ x1) :
    (((X \ {f | f ∈ [x1, y1]}) ∪ {f | f ∈ [x2, y2]}) \ {f | f ∈ [x2, y2]}) ∪ {f | f ∈ [x1, y1]} =
      (X \ {y2}) ∪ {y1} := by
  ext f
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_union, Set.mem_diff,
    Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨⟨⟨hf, hne1⟩ | hf, hne2⟩⟩ | hf | hf)
    · exact Or.inl ⟨hf, fun h => hne2 (Or.inr h)⟩
    · exact absurd hf hne2
    · subst hf; exact Or.inl ⟨h1, fun h => h12 h.symm⟩
    · exact Or.inr hf
  · rintro (⟨hf, hne⟩ | hf)
    · by_cases ha : f = x1
      · exact Or.inr (Or.inl ha)
      · by_cases hb : f = y1
        · exact Or.inr (Or.inr hb)
        · refine Or.inl ⟨Or.inl ⟨hf, ?_⟩, ?_⟩
          · rintro (h | h)
            · exact ha h
            · exact hb h
          · rintro (h | h)
            · subst h; exact h2 hf
            · exact hne h
    · exact Or.inr (Or.inr hf)

/-- The copy gadget on an arbitrary state in which `src` has the value `b`. -/
theorem setWin_copy {K : Set ℕ → Prop} {src : ℕ} {dl : Bool → ℕ} {X : Set ℕ} {b : Bool}
    (hX : lit src b ∈ X) (hX' : lit src (!b) ∉ X) (hdl : ∀ c d, dl c ≠ lit src d) :
    setWin K ([cpA src dl true, cpA src dl false].map FActDesc.toAction) X ↔
      K ((X \ {dl (!b)}) ∪ {dl b}) := by
  simp only [List.map_cons, List.map_nil]
  rw [setWin_pair]
  have happ : ∀ c (s : Set ℕ), (cpA src dl c).toAction.Applicable s ↔ lit src c ∈ s := fun c s => by
    rw [applicable_iff rfl]; simp [cpA]
  have hout : ∀ c (s : Set ℕ), (cpA src dl c).toAction.outcomes s =
      {(s \ {f | f ∈ [lit src c, dl c]}) ∪ {f | f ∈ [lit src (!c), dl (!c)]}} :=
    fun c s => outcomes_single (e := ([lit src (!c), dl (!c)], [lit src c, dl c])) rfl s
  simp only [happ, hout, Set.mem_singleton_iff, forall_eq]
  have hmem : ∀ c, lit src (!c) ∈ (X \ {f | f ∈ [lit src c, dl c]}) ∪
      {f | f ∈ [lit src (!c), dl (!c)]} := fun c => Or.inr (by simp)
  cases b
  · rw [or_iff_right (fun h => hX' h.1)]
    simp only [Bool.not_false, Bool.not_true] at hX hX' hmem ⊢
    rw [and_iff_right hX, and_iff_right (by simpa using hmem false)]
    rw [copy_set hX hX' (hdl _ _)]
  · rw [or_iff_left (fun h => hX' h.1)]
    simp only [Bool.not_false, Bool.not_true] at hX hX' hmem ⊢
    rw [and_iff_right hX, and_iff_right (by simpa using hmem true)]
    rw [copy_set hX hX' (hdl _ _)]

theorem enc_update' {V : List ℕ} {ρ : ℕ → Bool} {q r : ℕ} (hr : r ∈ V) (b : Bool) :
    (enc V ρ q \ {lit r (!b)}) ∪ {lit r b} = enc V (Function.update ρ r b) q := by
  rw [← enc_update hr b]; simp

theorem phasesWin_copy {V : List ℕ} {src dst : ℕ} (hs : src ∈ V) (hd : dst ∈ V) (hne : src ≠ dst)
    (K : Set ℕ → Prop) (ρ : ℕ → Bool) (q : ℕ) :
    phasesWin (opPhases (.copy src dst)) K (enc V ρ q) ↔
      opSem (.copy src dst) (fun ρ q => K (enc V ρ q)) ρ q := by
  simp only [opPhases, phasesWin_cons, phasesWin_nil, opSem]
  rw [setWin_copy (b := ρ src) ((lit_mem_enc hs _).2 rfl) (by rw [lit_mem_enc hs]; simp)
    (fun c d h => hne (lit_inj.1 h).1.symm), enc_update' hd]

/-! ## Add-only phases -/

/-- Deterministic actions without deletes and negative preconditions. -/
def AddOnly (a : FActDesc) : Prop := a.2.2.1 = [] ∧ ∃ add, a.2.2.2 = [(add, [])]

/-- All facts added by the actions. -/
def addsOf (L : List FActDesc) : Set ℕ := {f | ∃ a ∈ L, f ∈ (a.2.2.2.headI).1}

theorem mem_iff_getElem_or_eraseIdx {α : Type} {L : List α} {i : ℕ} (hi : i < L.length) {x : α} :
    x ∈ L ↔ x = L[i] ∨ x ∈ L.eraseIdx i := by
  rw [List.mem_eraseIdx_iff_getElem]
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    by_cases hji : j = i
    · subst hji; exact Or.inl rfl
    · exact Or.inr ⟨j, hj, hji, rfl⟩
  · rintro (rfl | ⟨j, hj, -, rfl⟩)
    · exact List.getElem_mem hi
    · exact List.getElem_mem hj

theorem addsOf_eraseIdx {L : List FActDesc} {i : ℕ} (hi : i < L.length) :
    addsOf L = {f | f ∈ (L[i].2.2.2.headI).1} ∪ addsOf (L.eraseIdx i) := by
  ext f
  simp only [addsOf, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨a, ha, hf⟩
    rcases (mem_iff_getElem_or_eraseIdx hi).1 ha with rfl | ha
    · exact Or.inl hf
    · exact Or.inr ⟨a, ha, hf⟩
  · rintro (hf | ⟨a, ha, hf⟩)
    · exact ⟨_, List.getElem_mem hi, hf⟩
    · exact ⟨a, (mem_iff_getElem_or_eraseIdx hi).2 (Or.inr ha), hf⟩

theorem outcomes_addOnly {a : FActDesc} (h : AddOnly a) (s : Set ℕ) :
    a.toAction.outcomes s = {s ∪ {f | f ∈ (a.2.2.2.headI).1}} := by
  obtain ⟨-, add, hadd⟩ := h
  rw [outcomes_single hadd]
  simp [hadd]

theorem applicable_addOnly {a : FActDesc} (h : AddOnly a) (s : Set ℕ) :
    a.toAction.Applicable s ↔ ∀ f ∈ a.2.1, f ∈ s := applicable_iff h.1 s

/-- **Add-only phases**: the final state does not depend on the order. -/
theorem setWin_addOnly (K : Set ℕ → Prop) : ∀ (n : ℕ) (L : List FActDesc) (s : Set ℕ),
    L.length = n → (∀ a ∈ L, AddOnly a) →
    (setWin K (L.map FActDesc.toAction) s ↔
      setWin (fun _ => True) (L.map FActDesc.toAction) s ∧ K (s ∪ addsOf L)) := by
  intro n
  induction n with
  | zero =>
    intro L s hn _
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    simp [setWin_nil, addsOf]
  | succ n ih =>
    intro L s hn hL
    have hne : L.map FActDesc.toAction ≠ [] := by
      intro h; simp at h; subst h; simp at hn
    rw [setWin_ne_nil _ hne, setWin_ne_nil _ hne]
    simp only [List.length_map, List.getElem_map, map_eraseIdx]
    have key : ∀ i (hi : i < L.length), ∀ s',
        setWin K ((L.eraseIdx i).map FActDesc.toAction) s' ↔
          setWin (fun _ => True) ((L.eraseIdx i).map FActDesc.toAction) s' ∧
            K (s' ∪ addsOf (L.eraseIdx i)) := fun i hi s' =>
      ih _ s' (by rw [List.length_eraseIdx_of_lt hi]; omega)
        (fun a ha => hL a (List.mem_of_mem_eraseIdx ha))
    constructor
    · rintro ⟨i, hi, happ, hall⟩
      have hA := hL _ (List.getElem_mem hi)
      rw [outcomes_addOnly hA] at hall
      have := (key i hi _).1 (hall _ rfl)
      refine ⟨⟨i, hi, happ, ?_⟩, ?_⟩
      · rw [outcomes_addOnly hA]; rintro s' rfl; exact this.1
      · have h2 := this.2
        rwa [Set.union_assoc, ← addsOf_eraseIdx hi] at h2
    · rintro ⟨⟨i, hi, happ, hall⟩, hK⟩
      have hA := hL _ (List.getElem_mem hi)
      rw [outcomes_addOnly hA] at hall
      refine ⟨i, hi, happ, ?_⟩
      rw [outcomes_addOnly hA]
      rintro s' rfl
      refine (key i hi _).2 ⟨hall _ rfl, ?_⟩
      rwa [Set.union_assoc, ← addsOf_eraseIdx hi]

/-- Add-only actions that are all applicable can be executed. -/
theorem setWin_allApp : ∀ (n : ℕ) (L : List FActDesc) (s : Set ℕ), L.length = n →
    (∀ a ∈ L, AddOnly a ∧ ∀ f ∈ a.2.1, f ∈ s) →
    setWin (fun _ => True) (L.map FActDesc.toAction) s := by
  intro n
  induction n with
  | zero =>
    intro L s hn _
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    simp [setWin_nil]
  | succ n ih =>
    intro L s hn hL
    have hne : L.map FActDesc.toAction ≠ [] := by
      intro h; simp at h; subst h; simp at hn
    rw [setWin_ne_nil _ hne]
    have h0 : 0 < L.length := by omega
    have hA := hL _ (List.getElem_mem h0)
    refine ⟨0, by simpa using h0, ?_, ?_⟩
    · simp only [List.getElem_map]; exact (applicable_addOnly hA.1 s).2 hA.2
    · simp only [List.getElem_map]
      rw [outcomes_addOnly hA.1]
      rintro s' rfl
      rw [map_eraseIdx]
      exact ih _ _ (by rw [List.length_eraseIdx_of_lt h0]; omega) fun a ha =>
        ⟨(hL a (List.mem_of_mem_eraseIdx ha)).1, fun f hf =>
          Or.inl ((hL a (List.mem_of_mem_eraseIdx ha)).2 f hf)⟩

/-- One step of the saturation game. -/
theorem setWin_true_step {L : List FActDesc} {s : Set ℕ} {i : ℕ} (hi : i < L.length)
    (hA : AddOnly L[i]) (happ : ∀ f ∈ L[i].2.1, f ∈ s)
    (h : setWin (fun _ => True) ((L.eraseIdx i).map FActDesc.toAction)
      (s ∪ {f | f ∈ (L[i].2.2.2.headI).1})) :
    setWin (fun _ => True) (L.map FActDesc.toAction) s := by
  have hne : L.map FActDesc.toAction ≠ [] := by
    intro h; simp at h; subst h; simp at hi
  rw [setWin_ne_nil _ hne]
  refine ⟨i, by simpa using hi, ?_, ?_⟩
  · simp only [List.getElem_map]; exact (applicable_addOnly hA s).2 happ
  · simp only [List.getElem_map]
    rw [outcomes_addOnly hA, map_eraseIdx]
    rintro s' rfl; exact h

/-! ## Clause checks -/

theorem addOnly_chkA (l : ℕ × Bool) : AddOnly (chkA l) := ⟨rfl, _, rfl⟩
theorem addOnly_finA : AddOnly finA := ⟨rfl, _, rfl⟩
theorem addOnly_clrA (W : List ℕ) : AddOnly (clrA W) := ⟨rfl, _, rfl⟩

theorem mem_encH_hlit {V W : List ℕ} {ρ : ℕ → Bool} {q v : ℕ} {b : Bool} :
    hlit v b ∈ encH V ρ q W ↔ v ∈ W ∧ ρ v = b := by
  simp only [encH, enc, Set.mem_union, Set.mem_setOf_eq, hlit_ne_lit, and_false, exists_false,
    hlit_ne_qF, or_false, false_or, hlit_inj]
  constructor
  · rintro ⟨w, hw, rfl, h⟩; exact ⟨hw, h.symm⟩
  · rintro ⟨hw, rfl⟩; exact ⟨v, hw, rfl, rfl⟩

theorem satF_not_mem_encH {V W : List ℕ} {ρ : ℕ → Bool} {q : ℕ} : satF ∉ encH V ρ q W := by
  simp [encH, enc]

theorem winF_not_mem_encH {V W : List ℕ} {ρ : ℕ → Bool} {q : ℕ} : winF ∉ encH V ρ q W := by
  simp [encH, enc]

/-- **The gadget of one clause**, on the helper copies of its registers. -/
theorem setWin_gadget {V : List ℕ} {ρ : ℕ → Bool} {q : ℕ} (C : Clause) (K : Set ℕ → Prop) :
    setWin K ((C.map chkA ++ [finA, clrA (cvars C)]).map FActDesc.toAction)
      (encH V ρ q (cvars C)) ↔
      SatC ρ C ∧ K (encH V ρ q (cvars C) ∪ addsOf (C.map chkA ++ [finA, clrA (cvars C)])) := by
  set L := C.map chkA ++ [finA, clrA (cvars C)]
  have hL : ∀ a ∈ L, AddOnly a := by
    intro a ha
    simp only [L, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ⟨l, -, rfl⟩ | rfl | rfl
    · exact addOnly_chkA l
    · exact addOnly_finA
    · exact addOnly_clrA _
  rw [setWin_addOnly K _ L _ rfl hL]
  refine and_congr_left fun _ => ?_
  have hvar : ∀ l ∈ C, l.1 ∈ cvars C := fun l hl => by
    simp only [cvars, List.mem_dedup, List.mem_map]; exact ⟨l, hl, rfl⟩
  have hlen : L.length = C.length + 2 := by simp [L]
  constructor
  · intro h
    have hne : L.map FActDesc.toAction ≠ [] := by simp [L]
    rw [setWin_ne_nil _ hne] at h
    obtain ⟨i, hi, happ, -⟩ := h
    simp only [List.length_map] at hi
    have hi2 : i < C.length + 2 := by rw [← hlen]; exact hi
    simp only [List.getElem_map] at happ
    rw [applicable_addOnly (hL _ (List.getElem_mem hi))] at happ
    rcases Nat.lt_or_ge i C.length with h1 | h1
    · have : L[i] = chkA C[i] := by
        simp only [L]; rw [List.getElem_append_left (by simpa using h1)]; simp
      rw [this] at happ
      have := happ _ (List.mem_singleton_self _)
      rw [mem_encH_hlit] at this
      exact ⟨_, List.getElem_mem h1, this.2⟩
    · rcases Nat.lt_or_ge i (C.length + 1) with h2 | h2
      · have : L[i] = finA := by
          simp only [L]; rw [List.getElem_append_right (by simpa using h1)]
          have : i - (C.map chkA).length = 0 := by simp; omega
          simp only [this]; rfl
        rw [this] at happ
        exact absurd (happ _ (List.mem_singleton_self _)) satF_not_mem_encH
      · have : L[i] = clrA (cvars C) := by
          simp only [L]; rw [List.getElem_append_right (by simpa using h1)]
          have : i - (C.map chkA).length = 1 := by simp; omega
          simp only [this]; rfl
        rw [this] at happ
        exact absurd (happ _ (List.mem_singleton_self _)) winF_not_mem_encH
  · rintro ⟨l, hl, hρ⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    have hj' : j < L.length := by omega
    have hLj : L[j] = chkA C[j] := by
      simp only [L]; rw [List.getElem_append_left (by simpa using hj)]; simp
    refine setWin_true_step hj' (hL _ (List.getElem_mem hj')) ?_ ?_
    · rw [hLj]; intro f hf
      simp only [chkA, List.mem_singleton] at hf; subst hf
      exact mem_encH_hlit.2 ⟨hvar _ hl, hρ⟩
    -- after the check: `fin`
    set C' := C.eraseIdx j
    have hE1 : L.eraseIdx j = C'.map chkA ++ [finA, clrA (cvars C)] := by
      simp only [L, C']
      rw [List.eraseIdx_append_of_lt_length (by simpa using hj), map_eraseIdx]
    rw [hE1, hLj]
    have hC' : C'.length = C.length - 1 := List.length_eraseIdx_of_lt hj
    have hk : C'.length < (C'.map chkA ++ [finA, clrA (cvars C)]).length := by simp
    refine setWin_true_step hk (by simpa using addOnly_finA) ?_ ?_
    · intro f hf
      have : (C'.map chkA ++ [finA, clrA (cvars C)])[C'.length] = finA := by
        rw [List.getElem_append_right (by simp)]; simp
      rw [this] at hf
      simp only [finA, List.mem_singleton] at hf; subst hf
      exact Or.inr (by simp [chkA])
    have hE2 : (C'.map chkA ++ [finA, clrA (cvars C)]).eraseIdx C'.length =
        C'.map chkA ++ [clrA (cvars C)] := by
      rw [List.eraseIdx_append_of_length_le (by simp)]; simp
    have hfin : (C'.map chkA ++ [finA, clrA (cvars C)])[C'.length] = finA := by
      rw [List.getElem_append_right (by simp)]; simp
    rw [hE2, hfin]
    have hk2 : C'.length < (C'.map chkA ++ [clrA (cvars C)]).length := by simp
    refine setWin_true_step hk2 (by simpa using addOnly_clrA (cvars C)) ?_ ?_
    · intro f hf
      have : (C'.map chkA ++ [clrA (cvars C)])[C'.length] = clrA (cvars C) := by
        rw [List.getElem_append_right (by simp)]; simp
      rw [this] at hf
      simp only [clrA, List.mem_singleton] at hf; subst hf
      exact Or.inr (by simp [finA])
    have hE3 : (C'.map chkA ++ [clrA (cvars C)]).eraseIdx C'.length = C'.map chkA := by
      rw [List.eraseIdx_append_of_length_le (by simp)]; simp
    have hclr : (C'.map chkA ++ [clrA (cvars C)])[C'.length] = clrA (cvars C) := by
      rw [List.getElem_append_right (by simp)]; simp
    rw [hE3, hclr]
    refine setWin_allApp _ _ _ rfl fun a ha => ?_
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 ha
    refine ⟨addOnly_chkA l', fun f hf => ?_⟩
    simp only [chkA, List.mem_singleton] at hf; subst hf
    have hv := hvar l' (List.mem_of_mem_eraseIdx hl')
    refine Or.inr ?_
    simp only [clrA, List.headI_cons, Set.mem_setOf_eq, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false]
    exact ⟨l'.1, hv, by cases l'.2 <;> simp⟩

theorem encH_congr {V W W' : List ℕ} {ρ : ℕ → Bool} {q : ℕ} (h : ∀ v, v ∈ W ↔ v ∈ W') :
    encH V ρ q W = encH V ρ q W' := by
  ext f; simp only [encH, Set.mem_union, Set.mem_setOf_eq, h]

theorem enc_eq_encH_nil {V : List ℕ} {ρ : ℕ → Bool} {q : ℕ} : enc V ρ q = encH V ρ q [] := by
  ext f; simp [encH]

/-- Copying registers into their helpers. -/
theorem phasesWin_hcopies {V : List ℕ} {ρ : ℕ → Bool} {q : ℕ} (R : List (List FActDesc))
    (K : Set ℕ → Prop) : ∀ (W' W0 : List ℕ), (∀ v ∈ W', v ∈ V) →
      (phasesWin (W'.map hcopy ++ R) K (encH V ρ q W0) ↔ phasesWin R K (encH V ρ q (W' ++ W0))) := by
  intro W'
  induction W' with
  | nil => intro W0 _; simp
  | cons v W' ih =>
    intro W0 hW
    have hv : v ∈ V := hW v (by simp)
    simp only [List.map_cons, List.cons_append, phasesWin_cons]
    have hX : lit v (ρ v) ∈ encH V ρ q W0 := Or.inl ((lit_mem_enc hv _).2 rfl)
    have hX' : lit v (!ρ v) ∉ encH V ρ q W0 := by
      simp only [encH, Set.mem_union, Set.mem_setOf_eq, lit_ne_hlit, and_false, exists_false,
        or_false, lit_mem_enc hv]; simp
    rw [hcopy, setWin_copy hX hX' (fun c d h => hlit_ne_lit _ _ _ _ h)]
    have : (encH V ρ q W0 \ {hlit v (!ρ v)}) ∪ {hlit v (ρ v)} = encH V ρ q (v :: W0) := by
      ext f
      simp only [encH, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq,
        Set.mem_singleton_iff, List.mem_cons]
      constructor
      · rintro (⟨h | ⟨w, hw, rfl⟩, hne⟩ | rfl)
        · exact Or.inl h
        · exact Or.inr ⟨w, Or.inr hw, rfl⟩
        · exact Or.inr ⟨v, Or.inl rfl, rfl⟩
      · rintro (h | ⟨w, rfl | hw, rfl⟩)
        · refine Or.inl ⟨Or.inl h, ?_⟩
          rintro rfl; simp [enc] at h
        · exact Or.inr rfl
        · by_cases hwv : w = v
          · subst hwv; exact Or.inr rfl
          · exact Or.inl ⟨Or.inr ⟨w, hw, rfl⟩, by simp [hwv]⟩
    rw [this, ih (v :: W0) fun u hu => hW u (by simp [hu])]
    rw [encH_congr (W' := v :: W' ++ W0) (fun u => by simp; tauto)]
    rfl

theorem reset_eq {V W : List ℕ} {ρ : ℕ → Bool} {q : ℕ} (C : Clause) :
    (encH V ρ q W ∪ addsOf (C.map chkA ++ [finA, clrA W])) \
      {f | f ∈ [satF, winF] ++ W.flatMap fun v => [hlit v true, hlit v false]} = enc V ρ q := by
  have hdel : ∀ f, f ∈ ([satF, winF] ++ W.flatMap fun v => [hlit v true, hlit v false]) ↔
      f = satF ∨ f = winF ∨ ∃ v ∈ W, ∃ b, f = hlit v b := fun f => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap]
    constructor
    · rintro ((h | h) | ⟨v, hv, h | h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨v, hv, true, h⟩)
      · exact Or.inr (Or.inr ⟨v, hv, false, h⟩)
    · rintro (h | h | ⟨v, hv, b, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · cases b
        · exact Or.inr ⟨v, hv, Or.inr h⟩
        · exact Or.inr ⟨v, hv, Or.inl h⟩
  ext f
  simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, hdel]
  constructor
  · rintro ⟨hf | hf, hne⟩
    · rcases hf with hf | hf
      · exact hf
      · obtain ⟨w, hw, rfl⟩ := hf
        exact absurd (Or.inr (Or.inr ⟨w, hw, _, rfl⟩)) hne
    · exfalso
      obtain ⟨a, ha, hf⟩ := hf
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ⟨l, -, rfl⟩ | rfl | rfl
      · simp only [chkA, List.headI_cons, List.mem_singleton] at hf; exact hne (Or.inl hf)
      · simp only [finA, List.headI_cons, List.mem_singleton] at hf; exact hne (Or.inr (Or.inl hf))
      · simp only [clrA, List.headI_cons, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
          or_false] at hf
        obtain ⟨v, hv, h | h⟩ := hf
        · exact hne (Or.inr (Or.inr ⟨v, hv, _, h⟩))
        · exact hne (Or.inr (Or.inr ⟨v, hv, _, h⟩))
  · intro h
    refine ⟨Or.inl (Or.inl h), ?_⟩
    simp only [enc, Set.mem_setOf_eq] at h
    rintro (rfl | rfl | ⟨v, -, b, rfl⟩) <;> rcases h with ⟨u, -, h⟩ | h <;> simp at h

theorem phasesWin_clause {V : List ℕ} (C : Clause) (hC : ∀ l ∈ C, l.1 ∈ V) (K : Set ℕ → Prop)
    (ρ : ℕ → Bool) (q : ℕ) :
    phasesWin (clausePhases C) K (enc V ρ q) ↔ SatC ρ C ∧ K (enc V ρ q) := by
  have hW : ∀ v ∈ cvars C, v ∈ V := fun v hv => by
    simp only [cvars, List.mem_dedup, List.mem_map] at hv
    obtain ⟨l, hl, rfl⟩ := hv; exact hC l hl
  conv_lhs => rw [clausePhases, enc_eq_encH_nil, phasesWin_hcopies _ K _ _ hW, List.append_nil,
    phasesWin_cons, setWin_gadget C]
  refine and_congr_right fun _ => ?_
  rw [phasesWin_cons, phasesWin_nil, List.map_cons, List.map_nil,
    setWin_det _ (rstA (cvars C)) (e := ([], [satF, winF] ++ (cvars C).flatMap fun v =>
      [hlit v true, hlit v false])) rfl rfl]
  rw [and_iff_right (by simp [rstA])]
  apply iff_of_eq
  congr 1
  rw [← reset_eq (W := cvars C) C]
  ext f; simp

theorem phasesWin_check {V : List ℕ} (Φ : List Clause) (hΦ : ∀ C ∈ Φ, ∀ l ∈ C, l.1 ∈ V)
    (K : Set ℕ → Prop) (ρ : ℕ → Bool) (q : ℕ) :
    phasesWin (opPhases (.check Φ)) K (enc V ρ q) ↔
      opSem (.check Φ) (fun ρ q => K (enc V ρ q)) ρ q := by
  simp only [opPhases, opSem]
  induction Φ with
  | nil => simp [phasesWin_nil]
  | cons C Φ ih =>
    rw [List.flatMap_cons, phasesWin_append, phasesWin_clause C (hΦ C (by simp))]
    rw [ih fun C' hC' => hΦ C' (by simp [hC'])]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-! ## Updates -/

theorem upd_eq {V : List ℕ} {q q' : ℕ} {sets : List (ℕ × Bool)} {ρ : ℕ → Bool}
    (hsets : ∀ l ∈ sets, l.1 ∈ V) (hnd : (sets.map Prod.fst).Nodup) :
    (enc V ρ q \ {f | f ∈ qF q :: sets.map (fun l => lit l.1 (!l.2))}) ∪
      {f | f ∈ qF q' :: sets.map (fun l => lit l.1 l.2)} = enc V (setAll ρ sets) q' := by
  have hval : ∀ v b, (v, b) ∈ sets → setAll ρ sets v = b := by
    intro v b hvb
    have huniq : ∀ c, (v, c) ∈ sets → c = b := fun c hc => by
      have := List.inj_on_of_nodup_map hnd hc hvb rfl
      simpa using this
    cases b
    · have : (v, true) ∉ sets := fun h => by simpa using huniq true h
      simp [setAll, this, hvb]
    · simp [setAll, hvb]
  have hval' : ∀ v, (∀ b, (v, b) ∉ sets) → setAll ρ sets v = ρ v := by
    intro v hv; simp [setAll, hv true, hv false]
  ext f
  simp only [enc, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, List.mem_cons, List.mem_map]
  constructor
  · rintro (⟨⟨v, hv, rfl⟩ | rfl, hne⟩ | rfl | ⟨l, hl, rfl⟩)
    · left; refine ⟨v, hv, ?_⟩
      by_cases hs : ∃ b, (v, b) ∈ sets
      · obtain ⟨b, hb⟩ := hs
        rw [hval v b hb]
        have : ρ v = b := by
          by_contra hne'
          apply hne; right; refine ⟨(v, b), hb, ?_⟩
          simp only [lit_inj, true_and]
          cases b <;> cases h : ρ v <;> simp_all
        rw [this]
      · push_neg at hs; rw [hval' v hs]
    · exact absurd (Or.inl rfl) hne
    · right; rfl
    · left; exact ⟨l.1, hsets l hl, by rw [hval l.1 l.2 hl]⟩
  · rintro (⟨v, hv, rfl⟩ | rfl)
    · by_cases hs : ∃ b, (v, b) ∈ sets
      · obtain ⟨b, hb⟩ := hs
        right; right; exact ⟨(v, b), hb, by rw [hval v b hb]⟩
      · push_neg at hs
        rw [hval' v hs]
        left
        refine ⟨Or.inl ⟨v, hv, rfl⟩, ?_⟩
        rintro (h | ⟨l, hl, h⟩)
        · simp at h
        · simp only [lit_inj] at h
          obtain ⟨rfl, -⟩ := h
          exact hs l.2 hl
    · right; left; rfl

theorem phasesWin_upd {V : List ℕ} {q₀ q' : ℕ} {pre sets : List (ℕ × Bool)}
    (hpre : ∀ l ∈ pre, l.1 ∈ V) (hsets : ∀ l ∈ sets, l.1 ∈ V) (hnd : (sets.map Prod.fst).Nodup)
    (K : Set ℕ → Prop) (ρ : ℕ → Bool) (q : ℕ) :
    phasesWin (opPhases (.upd q₀ pre q' sets)) K (enc V ρ q) ↔
      opSem (.upd q₀ pre q' sets) (fun ρ q => K (enc V ρ q)) ρ q := by
  simp only [opPhases, opSem, phasesWin_cons, phasesWin_nil, List.map_cons, List.map_nil]
  rw [setWin_det _ (updA q₀ pre q' sets) (e := (qF q' :: sets.map (fun l => lit l.1 l.2),
    qF q₀ :: sets.map (fun l => lit l.1 (!l.2)))) rfl rfl]
  have happ : (∀ f ∈ (updA q₀ pre q' sets).2.1, f ∈ enc V ρ q) ↔
      q = q₀ ∧ ∀ l ∈ pre, ρ l.1 = l.2 := by
    simp only [updA, List.mem_cons, forall_eq_or_imp, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, qF_mem_enc]
    rw [eq_comm (a := q₀)]
    exact and_congr_right fun _ => forall₂_congr fun l hl => lit_mem_enc (hpre l hl) _
  rw [happ, and_assoc]
  refine and_congr_right fun hq => and_congr_right fun _ => ?_
  subst hq
  rw [upd_eq hsets hnd]

/-! ## Operations and blocks -/

/-- The registers an operation uses are among `V`. -/
def OpWF (V : List ℕ) : Op → Prop
  | .choice r => r ∈ V
  | .nature r => r ∈ V
  | .copy s d => s ∈ V ∧ d ∈ V ∧ s ≠ d
  | .check Φ => ∀ C ∈ Φ, ∀ l ∈ C, l.1 ∈ V
  | .upd _ pre _ sets => (∀ l ∈ pre, l.1 ∈ V) ∧ (∀ l ∈ sets, l.1 ∈ V) ∧ (sets.map Prod.fst).Nodup

/-- **Correctness of the gadget of an operation.** -/
theorem phasesWin_op {V : List ℕ} {op : Op} (h : OpWF V op) (K : Set ℕ → Prop)
    (ρ : ℕ → Bool) (q : ℕ) :
    phasesWin (opPhases op) K (enc V ρ q) ↔ opSem op (fun ρ q => K (enc V ρ q)) ρ q := by
  cases op with
  | choice r => exact phasesWin_choice h K ρ q
  | nature r => exact phasesWin_nature h K ρ q
  | copy s d => exact phasesWin_copy h.1 h.2.1 h.2.2 K ρ q
  | check Φ => exact phasesWin_check Φ h K ρ q
  | upd q₀ pre q' sets => exact phasesWin_upd h.1 h.2.1 h.2.2 K ρ q

/-- The meaning of a block of operations. -/
def blockSem (ops : List Op) (K : (ℕ → Bool) → ℕ → Prop) : (ℕ → Bool) → ℕ → Prop :=
  ops.foldr (fun op K' => opSem op K') K

theorem opSem_congr (op : Op) {K K' : (ℕ → Bool) → ℕ → Prop} (h : ∀ ρ q, K ρ q ↔ K' ρ q)
    (ρ : ℕ → Bool) (q : ℕ) : opSem op K ρ q ↔ opSem op K' ρ q := by
  cases op <;> simp only [opSem, h]

/-- **Correctness of a block.** -/
theorem phasesWin_block {V : List ℕ} : ∀ (ops : List Op), (∀ op ∈ ops, OpWF V op) →
    ∀ (K : Set ℕ → Prop) (ρ : ℕ → Bool) (q : ℕ),
    phasesWin (ops.flatMap opPhases) K (enc V ρ q) ↔ blockSem ops (fun ρ q => K (enc V ρ q)) ρ q
  | [], _, K, ρ, q => by simp [phasesWin_nil, blockSem]
  | op :: ops, h, K, ρ, q => by
    rw [List.flatMap_cons, phasesWin_append]
    have ih := phasesWin_block ops (fun o ho => h o (by simp [ho])) K
    have hK : phasesWin (ops.flatMap opPhases) K =
        fun s => phasesWin (ops.flatMap opPhases) K s := rfl
    -- reduce the inner condition to encoded states
    have key : ∀ (K' : Set ℕ → Prop), (∀ ρ q, K' (enc V ρ q) ↔
        blockSem ops (fun ρ q => K (enc V ρ q)) ρ q) →
        (phasesWin (opPhases op) K' (enc V ρ q) ↔
          blockSem (op :: ops) (fun ρ q => K (enc V ρ q)) ρ q) := fun K' hK' => by
      rw [phasesWin_op (h op (by simp)) K' ρ q]
      exact opSem_congr op hK' ρ q
    exact key _ ih

end DB



end FOND
