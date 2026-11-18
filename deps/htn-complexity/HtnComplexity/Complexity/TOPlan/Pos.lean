import HtnComplexity.Complexity.TOPlan.Kit
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Positions in a serialised instance description, and what they carry

The planner of `HtnComplexity/Complexity/TOPlan/` reads the serialisation
`HTN.Syn.instSer q = A ++ B ++ C ++ D ++ E` of an instance description (`A` the initial state,
`B` the goal, `C` the identifiers, `D` the ordering pairs, `E` the labels of the initial task
network).  It names an identifier, an ordering pair, … by the *position* of its entry, i.e. by
the suffix of the code that starts there.  This file provides

* the extraction functions `HTN.Syn.TOPlan.dropBL` (drop the first serialised list),
  `HTN.Syn.TOPlan.bpre` (the self-delimiting numeral at the front) and `HTN.Syn.TOPlan.dpre` (the
  doubled self-delimiting numeral at the front), all functions of Cobham's class;
* the positions: `HTN.Syn.TOPlan.idPos x s` (an entry of the identifier list starts at `s`) and
  `HTN.Syn.TOPlan.edgePos x e` (an entry of the list of ordering pairs starts at `e`), with what
  they carry: `HTN.Syn.TOPlan.nvAt s`, the numeral of the identifier, and
  `HTN.Syn.TOPlan.srcD e`, `HTN.Syn.TOPlan.tgtD e`, the doubled numerals of the two endpoints;
* the dictionary between positions and list elements (`HTN.Syn.TOPlan.exists_idPos_iff`,
  `HTN.Syn.TOPlan.exists_edgePos_iff`);
* the label of an identifier, read off the label list (`HTN.Syn.TOPlan.actIs`,
  `HTN.Syn.TOPlan.compIs`, `HTN.Syn.TOPlan.isComp` and their meaning).
-/

namespace HTN

namespace Syn

namespace TOPlan

open PTime Compress

/-! ### Doubled self-delimiting strings (the recogniser of `Space/SeqStr.lean`) -/

/-- The states of the recogniser of `(111b)*(10)`. -/
inductive BdSt
  | g0 | g1 | g2 | g3 | acc | dead
  deriving DecidableEq, Fintype

/-- The transition of the recogniser of doubled self-delimiting strings. -/
def bdStep : BdSt → Bool → BdSt
  | .g0, true => .g1
  | .g1, false => .acc
  | .g1, true => .g2
  | .g2, true => .g3
  | .g3, _ => .g0
  | _, _ => .dead

/-- **Is the string a doubled self-delimiting string `dbl (bstr u)`?** -/
def isBDs (D : List Bool) : Bool := decide (D.foldl bdStep .g0 = .acc)

theorem foldl_bdStep_dead (x : List Bool) : x.foldl bdStep .dead = .dead := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simpa [bdStep] using ih

theorem foldl_bdStep_acc (x : List Bool) (hx : x ≠ []) : x.foldl bdStep .acc = .dead := by
  cases x with
  | nil => exact absurd rfl hx
  | cons b x => cases b <;> simpa [bdStep] using foldl_bdStep_dead x

theorem dbl_bstr_cons' (b : Bool) (u : List Bool) :
    dbl (bstr (b :: u)) = true :: true :: true :: b :: dbl (bstr u) := by
  simp [bstr_cons, dbl_cons]

theorem dbl_bstr_nil : dbl (bstr []) = [true, false] := rfl

theorem bds_of_foldl : ∀ D : List Bool, D.foldl bdStep .g0 = .acc → ∃ u, D = dbl (bstr u)
  | [], h => by simp at h
  | [false], h => by simp [bdStep] at h
  | [true], h => by simp [bdStep] at h
  | false :: _ :: D, h => by simp [bdStep, foldl_bdStep_dead] at h
  | true :: false :: D, h => by
    rcases eq_or_ne D [] with rfl | hD
    · exact ⟨[], rfl⟩
    · simp [bdStep, foldl_bdStep_acc D hD] at h
  | [true, true], h => by simp [bdStep] at h
  | true :: true :: false :: D, h => by simp [bdStep, foldl_bdStep_dead] at h
  | [true, true, true], h => by simp [bdStep] at h
  | true :: true :: true :: b :: D, h => by
    obtain ⟨u, rfl⟩ := bds_of_foldl D (by cases b <;> simpa [bdStep] using h)
    exact ⟨b :: u, by rw [dbl_bstr_cons']⟩

theorem isBDs_iff (D : List Bool) : isBDs D = true ↔ ∃ u, D = dbl (bstr u) := by
  rw [isBDs, decide_eq_true_eq]
  constructor
  · exact bds_of_foldl D
  · rintro ⟨u, rfl⟩
    induction u with
    | nil => rfl
    | cons b u ih => rw [dbl_bstr_cons']; cases b <;> simpa [bdStep] using ih

theorem cobhamB_isBDs {a : Fn} (ha : Cobham a) : CobhamB fun args => isBDs (a args) := by
  obtain ⟨f, hf, hFf⟩ := (polyTimeFun_dfa BdSt.g0 bdStep (fun s => decide (s = .acc))).cobham
  refine (Cobham.comp hf (hs := [a]) (by simpa using ha)).of_eq' fun args => ?_
  simp only [compFn, List.map_cons, List.map_nil]
  exact (hFf (a args)).symm

/-- A doubled self-delimiting string followed by junk determines both. -/
theorem dbl_bstr_parse : ∀ {w w' r r' : List Bool},
    dbl (bstr w) ++ r = dbl (bstr w') ++ r' → w = w' ∧ r = r'
  | [], [], r, r', h => ⟨rfl, by simpa [dbl_bstr_nil] using h⟩
  | [], c :: u, r, r', h => by rw [dbl_bstr_nil, dbl_bstr_cons'] at h; simp at h
  | b :: u, [], r, r', h => by rw [dbl_bstr_nil, dbl_bstr_cons'] at h; simp at h
  | b :: u, c :: u', r, r', h => by
    simp only [dbl_bstr_cons', List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨h1, h2⟩ := dbl_bstr_parse h.2
    exact ⟨by rw [h.1, h1], h2⟩

theorem dbl_injective' : Function.Injective dbl := by
  intro u v h
  induction u generalizing v with
  | nil => cases v with
    | nil => rfl
    | cons b v => simp [dbl_cons] at h
  | cons b u ih => cases v with
    | nil => simp [dbl_cons] at h
    | cons c v =>
      simp only [dbl_cons, List.cons.injEq, true_and] at h
      rw [h.1, ih h.2]

/-! ### Extraction functions -/

/-- The rest of a string after its first serialised list. -/
def dropBL (z : List Bool) : List Bool := findTail (fun s => blistB (cutS z s)) z

/-- The self-delimiting string at the front of a string. -/
def bpre (z : List Bool) : List Bool := cutS z (findTail (fun t => entryB (true :: cutS z t)) z)

/-- The doubled self-delimiting string at the front of a string. -/
def dpre (z : List Bool) : List Bool := cutS z (findTail (fun t => isBDs (cutS z t)) z)

theorem cutS_suffix_append {z s : List Bool} (hs : s <:+ z) : cutS z s ++ s = z :=
  suffix_take_append hs

theorem dropBL_blist (l : List (List Bool)) (r : List Bool) : dropBL (blist l ++ r) = r := by
  refine findTail_eq (List.suffix_append _ _) ?_ fun s hs hlen => ?_
  · rw [cutS_append]; exact blistB_iff.2 ⟨l, rfl⟩
  · by_contra hc
    rw [Bool.not_eq_false] at hc
    obtain ⟨l', hl'⟩ := blistB_iff.1 hc
    have h := cutS_suffix_append hs
    rw [hl'] at h
    obtain ⟨-, rfl⟩ := blist_parse h
    exact lt_irrefl _ hlen

theorem bpre_bstr (w r : List Bool) : bpre (bstr w ++ r) = bstr w := by
  have hft : findTail (fun t => entryB (true :: cutS (bstr w ++ r) t)) (bstr w ++ r) = r := by
    refine findTail_eq (List.suffix_append _ _) ?_ fun s hs hlen => ?_
    · rw [cutS_append]; exact entryB_iff.2 ⟨w, rfl⟩
    · by_contra hc
      rw [Bool.not_eq_false] at hc
      obtain ⟨w', hw'⟩ := entryB_iff.1 hc
      have h := cutS_suffix_append hs
      rw [List.cons.inj hw' |>.2] at h
      obtain ⟨-, rfl⟩ := bstr_parse h
      exact lt_irrefl _ hlen
  rw [bpre, hft, cutS_append]

theorem dpre_dbl_bstr (w r : List Bool) : dpre (dbl (bstr w) ++ r) = dbl (bstr w) := by
  have hft : findTail (fun t => isBDs (cutS (dbl (bstr w) ++ r) t)) (dbl (bstr w) ++ r) = r := by
    refine findTail_eq (List.suffix_append _ _) ?_ fun s hs hlen => ?_
    · rw [cutS_append]; exact (isBDs_iff _).2 ⟨w, rfl⟩
    · by_contra hc
      rw [Bool.not_eq_false] at hc
      obtain ⟨w', hw'⟩ := (isBDs_iff _).1 hc
      have h := cutS_suffix_append hs
      rw [hw'] at h
      obtain ⟨-, rfl⟩ := dbl_bstr_parse h
      exact lt_irrefl _ hlen
  rw [dpre, hft, cutS_append]

theorem cobham_dropBL {a : Fn} (ha : Cobham a) : Cobham fun args => dropBL (a args) := by
  have hp : CobhamB fun args : Args => blistB (cutS (a args.tail) (args.getD 0 [])) :=
    cobhamB_blistB (cobham_cut (cobham_tailArgs ha) (Cobham.proj 0))
  exact (cobham_findTailC hp ha).of_eq' fun args => by simp [findTailL, dropBL]

theorem cobham_bpre {a : Fn} (ha : Cobham a) : Cobham fun args => bpre (a args) := by
  have hp : CobhamB fun args : Args =>
      entryB (true :: cutS (a args.tail) (args.getD 0 [])) :=
    cobhamB_entryB (cobham_consB (cobhamB_const true)
      (cobham_cut (cobham_tailArgs ha) (Cobham.proj 0)))
  exact (cobham_cut ha (cobham_findTailC hp ha)).of_eq' fun args => by
    simp [findTailL, bpre]

theorem cobham_dpre {a : Fn} (ha : Cobham a) : Cobham fun args => dpre (a args) := by
  have hp : CobhamB fun args : Args => isBDs (cutS (a args.tail) (args.getD 0 [])) :=
    cobhamB_isBDs (cobham_cut (cobham_tailArgs ha) (Cobham.proj 0))
  exact (cobham_cut ha (cobham_findTailC hp ha)).of_eq' fun args => by
    simp [findTailL, dpre]

/-! ### The five lists of a serialised instance -/

/-- The code of the labels. -/
def zE (q : InstDesc) : List Bool := blist (q.tnI.lbl.map serLbl)

/-- The code of the ordering pairs and the labels. -/
def zD (q : InstDesc) : List Bool := blist (q.tnI.ordList.map serPair) ++ zE q

/-- The code of the identifiers, the ordering pairs and the labels. -/
def zC (q : InstDesc) : List Bool := blist (q.tnI.ids.map bitsOfNat) ++ zD q

/-- The code of the goal and the initial task network. -/
def zB (q : InstDesc) : List Bool := blist (q.goalList.map bitsOfNat) ++ zC q

theorem instSer_eq (q : InstDesc) : instSer q = blist (q.initList.map bitsOfNat) ++ zB q := by
  simp [instSer, serNatList, tnSer, serPairList, serLblList, zB, zC, zD, zE, List.append_assoc]

/-- The suffix after the initial state. -/
def yB (x : List Bool) : List Bool := dropBL x
/-- The suffix after the goal. -/
def yC (x : List Bool) : List Bool := dropBL (yB x)
/-- The suffix after the identifiers. -/
def yD (x : List Bool) : List Bool := dropBL (yC x)
/-- The suffix after the ordering pairs. -/
def yE (x : List Bool) : List Bool := dropBL (yD x)

theorem yB_instSer (q : InstDesc) : yB (instSer q) = zB q := by
  rw [yB, instSer_eq, dropBL_blist]

theorem yC_instSer (q : InstDesc) : yC (instSer q) = zC q := by
  rw [yC, yB_instSer, zB, dropBL_blist]

theorem yD_instSer (q : InstDesc) : yD (instSer q) = zD q := by
  rw [yD, yC_instSer, zC, dropBL_blist]

theorem yE_instSer (q : InstDesc) : yE (instSer q) = zE q := by
  rw [yE, yD_instSer, zD, dropBL_blist]

theorem zB_suffix (q : InstDesc) : zB q <:+ instSer q := by
  rw [instSer_eq]; exact List.suffix_append _ _

theorem zC_suffix (q : InstDesc) : zC q <:+ instSer q :=
  (List.suffix_append _ _).trans (zB_suffix q)

theorem zD_suffix (q : InstDesc) : zD q <:+ instSer q :=
  (List.suffix_append _ _).trans (zC_suffix q)

theorem cobham_yB {a : Fn} (ha : Cobham a) : Cobham fun args => yB (a args) := cobham_dropBL ha
theorem cobham_yC {a : Fn} (ha : Cobham a) : Cobham fun args => yC (a args) :=
  cobham_dropBL (cobham_yB ha)
theorem cobham_yD {a : Fn} (ha : Cobham a) : Cobham fun args => yD (a args) :=
  cobham_dropBL (cobham_yC ha)
theorem cobham_yE {a : Fn} (ha : Cobham a) : Cobham fun args => yE (a args) :=
  cobham_dropBL (cobham_yD ha)

/-! ### Positions of entries -/

/-- **An entry of the serialised list that starts `y` starts at `s`.** -/
def entPos (y s : List Bool) : Bool :=
  decide (s <:+ y) && entriesB (cutS y s) && s.headD false

theorem entPos_iff {α : Type} (f : α → List Bool) (l : List α) (z s : List Bool) :
    entPos (blist (l.map f) ++ z) s = true ↔
      ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ s = blist ((a :: l₂).map f) ++ z := by
  constructor
  · intro h
    simp only [entPos, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨e, he⟩ := entriesB_iff.1 h2
    have hsplit : entriesEnc e ++ s = blist (l.map f) ++ z := by
      rw [← he]; exact cutS_suffix_append h1
    obtain ⟨l₂, hl, hr⟩ := entriesEnc_align e s _ z hsplit
    cases l₂ with
    | nil => rw [hr] at h3; simp at h3
    | cons w l₂' =>
      obtain ⟨L₁, L₂, rfl, hL₁, hL₂⟩ := List.map_eq_append_iff.1 hl
      obtain ⟨a, L₃, rfl, ha, hL₃⟩ := List.map_eq_cons_iff.1 hL₂
      refine ⟨L₁, a, L₃, rfl, ?_⟩
      rw [hr, List.map_cons, ha, hL₃]
  · rintro ⟨l₁, a, l₂, rfl, rfl⟩
    have hy : blist ((l₁ ++ a :: l₂).map f) ++ z
        = entriesEnc (l₁.map f) ++ (blist ((a :: l₂).map f) ++ z) := by
      rw [List.map_append, blist_append_eq, List.append_assoc]
    simp only [entPos, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨entriesEnc (l₁.map f), hy.symm⟩, ?_⟩, ?_⟩
    · rw [hy, cutS_append]; exact entriesB_iff.2 ⟨_, rfl⟩
    · simp [blist_cons]

theorem cobhamB_entPos {y s : Fn} (hy : Cobham y) (hs : Cobham s) :
    CobhamB fun args => entPos (y args) (s args) :=
  ((cobhamB_isSuffix hs hy).and (cobhamB_entriesB (cobham_cut hy hs))).and (cobhamB_head hs)

/-- **An entry of the identifier list starts at `s`.** -/
def idPos (x s : List Bool) : Bool := entPos (yC x) s

/-- **An entry of the list of ordering pairs starts at `e`.** -/
def edgePos (x e : List Bool) : Bool := entPos (yD x) e

/-- The numeral of the identifier whose entry starts at `s`. -/
def nvAt (s : List Bool) : List Bool := bpre s.tail

/-- The doubled numeral of a number: the form in which numbers occur inside the entries of the
lists of pairs and of labels. -/
def key (u : ℕ) : List Bool := dbl (serNat u)

theorem key_injective : Function.Injective key := fun a b h =>
  bitsOfNat_injective (bstr_parse (r := []) (s := [])
    (by simpa using dbl_injective' h)).1

/-- The doubled numeral of the source of the pair whose entry starts at `e`. -/
def srcD (e : List Bool) : List Bool := dpre e.tail

/-- The doubled numeral of the target of the pair whose entry starts at `e`. -/
def tgtD (e : List Bool) : List Bool := dpre (e.tail.drop (srcD e).length)

theorem idPos_iff (q : InstDesc) (s : List Bool) :
    idPos (instSer q) s = true ↔
      ∃ l₁ u l₂, q.tnI.ids = l₁ ++ u :: l₂ ∧ s = blist ((u :: l₂).map bitsOfNat) ++ zD q := by
  rw [idPos, yC_instSer, zC, entPos_iff]

theorem edgePos_iff (q : InstDesc) (e : List Bool) :
    edgePos (instSer q) e = true ↔
      ∃ E₁ p E₂, q.tnI.ordList = E₁ ++ p :: E₂ ∧ e = blist ((p :: E₂).map serPair) ++ zE q := by
  rw [edgePos, yD_instSer, zD, entPos_iff]

theorem nvAt_eq (u : ℕ) (l : List ℕ) (z : List Bool) :
    nvAt (blist ((u :: l).map bitsOfNat) ++ z) = serNat u := by
  simp only [nvAt, List.map_cons, blist_cons, List.cons_append, List.tail_cons, List.append_assoc]
  exact bpre_bstr _ _

theorem srcD_tgtD_eq (p : ℕ × ℕ) (l : List (ℕ × ℕ)) (z : List Bool) :
    srcD (blist ((p :: l).map serPair) ++ z) = key p.1 ∧
      tgtD (blist ((p :: l).map serPair) ++ z) = key p.2 := by
  have htail : (blist ((p :: l).map serPair) ++ z).tail
      = dbl (bstr (bitsOfNat p.1)) ++ (dbl (bstr (bitsOfNat p.2)) ++
        (false :: (blist (l.map serPair) ++ z))) := by
    rw [List.map_cons, blist_cons, List.cons_append, List.tail_cons, bstr_eq_dbl (serPair p),
      serPair, dbl_append]
    simp only [serNat, List.append_assoc, List.cons_append, List.nil_append]
  have hs : srcD (blist ((p :: l).map serPair) ++ z) = key p.1 := by
    rw [srcD, htail, dpre_dbl_bstr]; rfl
  refine ⟨hs, ?_⟩
  rw [tgtD, hs, htail, show (key p.1).length = (dbl (bstr (bitsOfNat p.1))).length from rfl,
    List.drop_left, dpre_dbl_bstr]
  rfl

theorem cobham_nvAt {s : Fn} (hs : Cobham s) : Cobham fun args => nvAt (s args) :=
  cobham_bpre ((cobham_drop (cobham_const [false]) hs).of_eq' fun args => by simp)

theorem cobham_srcD {e : Fn} (he : Cobham e) : Cobham fun args => srcD (e args) :=
  cobham_dpre ((cobham_drop (cobham_const [false]) he).of_eq' fun args => by simp)

theorem cobham_tgtD {e : Fn} (he : Cobham e) : Cobham fun args => tgtD (e args) :=
  cobham_dpre (cobham_drop (cobham_srcD he)
    ((cobham_drop (cobham_const [false]) he).of_eq' fun args => by simp))

theorem cobhamB_idPos {x s : Fn} (hx : Cobham x) (hs : Cobham s) :
    CobhamB fun args => idPos (x args) (s args) :=
  cobhamB_entPos (cobham_yC hx) hs

theorem cobhamB_edgePos {x s : Fn} (hx : Cobham x) (hs : Cobham s) :
    CobhamB fun args => edgePos (x args) (s args) :=
  cobhamB_entPos (cobham_yD hx) hs

/-! ### The dictionary between positions and list elements -/

theorem idPos_suffix {q : InstDesc} {s : List Bool} (h : idPos (instSer q) s = true) :
    s <:+ instSer q := by
  obtain ⟨l₁, u, l₂, hids, rfl⟩ := (idPos_iff q s).1 h
  refine List.IsSuffix.trans ⟨entriesEnc (l₁.map bitsOfNat), ?_⟩ (zC_suffix q)
  rw [zC, hids, List.map_append, blist_append_eq, List.append_assoc]

/-- An identifier position carries the numeral of a listed identifier. -/
theorem idPos_val {q : InstDesc} {s : List Bool} (h : idPos (instSer q) s = true) :
    ∃ u ∈ q.tnI.ids, nvAt s = serNat u := by
  obtain ⟨l₁, u, l₂, hids, rfl⟩ := (idPos_iff q s).1 h
  exact ⟨u, by rw [hids]; simp, nvAt_eq _ _ _⟩

/-- Every listed identifier is carried by some identifier position. -/
theorem exists_idPos_of_mem {q : InstDesc} {u : ℕ} (hu : u ∈ q.tnI.ids) :
    ∃ s, s <:+ instSer q ∧ idPos (instSer q) s = true ∧ nvAt s = serNat u := by
  obtain ⟨l₁, l₂, hids⟩ := List.append_of_mem hu
  have hpos : idPos (instSer q) (blist ((u :: l₂).map bitsOfNat) ++ zD q) = true :=
    (idPos_iff q _).2 ⟨l₁, u, l₂, hids, rfl⟩
  exact ⟨_, idPos_suffix hpos, hpos, nvAt_eq _ _ _⟩

theorem exists_idPos_iff (q : InstDesc) (P : List Bool → Prop) :
    (∃ s, s <:+ instSer q ∧ idPos (instSer q) s = true ∧ P (nvAt s)) ↔
      ∃ u ∈ q.tnI.ids, P (serNat u) := by
  constructor
  · rintro ⟨s, -, hs, hP⟩
    obtain ⟨u, hu, hv⟩ := idPos_val hs
    exact ⟨u, hu, hv ▸ hP⟩
  · rintro ⟨u, hu, hP⟩
    obtain ⟨s, hsx, hs, hv⟩ := exists_idPos_of_mem hu
    exact ⟨s, hsx, hs, hv ▸ hP⟩

theorem edgePos_suffix {q : InstDesc} {e : List Bool} (h : edgePos (instSer q) e = true) :
    e <:+ instSer q := by
  obtain ⟨E₁, p, E₂, hord, rfl⟩ := (edgePos_iff q e).1 h
  refine List.IsSuffix.trans ⟨entriesEnc (E₁.map serPair), ?_⟩ (zD_suffix q)
  rw [zD, hord, List.map_append, blist_append_eq, List.append_assoc]

/-- An edge position carries the doubled numerals of a listed pair. -/
theorem edgePos_val {q : InstDesc} {e : List Bool} (h : edgePos (instSer q) e = true) :
    ∃ p ∈ q.tnI.ordList, srcD e = key p.1 ∧ tgtD e = key p.2 := by
  obtain ⟨E₁, p, E₂, hord, rfl⟩ := (edgePos_iff q e).1 h
  exact ⟨p, by rw [hord]; simp, srcD_tgtD_eq _ _ _⟩

theorem exists_edgePos_iff (q : InstDesc) (P : List Bool → List Bool → Prop) :
    (∃ e, e <:+ instSer q ∧ edgePos (instSer q) e = true ∧ P (srcD e) (tgtD e)) ↔
      ∃ p ∈ q.tnI.ordList, P (key p.1) (key p.2) := by
  constructor
  · rintro ⟨e, -, he, hP⟩
    obtain ⟨p, hp, h1, h2⟩ := edgePos_val he
    exact ⟨p, hp, h1 ▸ h2 ▸ hP⟩
  · rintro ⟨p, hp, hP⟩
    obtain ⟨E₁, E₂, hord⟩ := List.append_of_mem hp
    have hpos : edgePos (instSer q) (blist ((p :: E₂).map serPair) ++ zE q) = true :=
      (edgePos_iff q _).2 ⟨E₁, p, E₂, hord, rfl⟩
    obtain ⟨h1, h2⟩ := srcD_tgtD_eq p E₂ (zE q)
    exact ⟨_, edgePos_suffix hpos, hpos, by rw [h1, h2]; exact hP⟩

/-! ### Labels -/

/-- The lookup test of `SerLookup.lean` for the identifier whose entry starts at `s`. -/
def lblB (K x s : List Bool) : Bool := firstLabelS K (yE x) (nvAt s)

theorem lblB_iff (q : InstDesc) {s : List Bool} {u : ℕ} (hs : nvAt s = serNat u)
    (K : List Bool) :
    lblB K (instSer q) s = true ↔
      match q.tnI.lbl.lookup u with
      | some (b, n) => K <+: (b :: bstr (bitsOfNat n))
      | none => False := by
  rw [lblB, yE_instSer, hs, firstLabelS_eq, zE, firstLabelB_iff]
  exact serLbl_first_iff _ _ _

/-- The identifier is labelled with the action `a`. -/
def actIs (a : ℕ) (x s : List Bool) : Bool :=
  lblB (false :: serNat a) x s || (decide (a = 0) && !lblB [] x s)

/-- The identifier is labelled with the compound task `c`. -/
def compIs (c : ℕ) (x s : List Bool) : Bool := lblB (true :: serNat c) x s

/-- The identifier is labelled with a compound task. -/
def isComp (x s : List Bool) : Bool := lblB [true] x s

theorem serNat_prefix_iff (a n : ℕ) : serNat a <+: bstr (bitsOfNat n) ↔ a = n := by
  rw [show bstr (bitsOfNat n) = bstr (bitsOfNat n) ++ [] from (List.append_nil _).symm]
  exact (bstr_prefix_iff _ _ _).trans ⟨fun h => bitsOfNat_injective h, fun h => by rw [h]⟩

theorem actIs_iff (q : InstDesc) {s : List Bool} {u : ℕ} (hs : nvAt s = serNat u) (a : ℕ) :
    actIs a (instSer q) s = true ↔ q.tnI.label u = Sum.inl a := by
  simp only [actIs, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    TnDesc.label]
  rw [lblB_iff q hs, show lblB [] (instSer q) s = false ↔ ¬ lblB [] (instSer q) s = true by simp,
    lblB_iff q hs]
  rcases q.tnI.lbl.lookup u with _ | ⟨b, n⟩
  · simp [eq_comm]
  · cases b <;> simp [List.cons_prefix_cons, serNat_prefix_iff, eq_comm]

theorem compIs_iff (q : InstDesc) {s : List Bool} {u : ℕ} (hs : nvAt s = serNat u) (c : ℕ) :
    compIs c (instSer q) s = true ↔ q.tnI.label u = Sum.inr c := by
  rw [compIs, lblB_iff q hs]
  simp only [TnDesc.label]
  rcases q.tnI.lbl.lookup u with _ | ⟨b, n⟩
  · simp
  · cases b <;> simp [List.cons_prefix_cons, serNat_prefix_iff, eq_comm]

theorem isComp_iff (q : InstDesc) {s : List Bool} {u : ℕ} (hs : nvAt s = serNat u) :
    isComp (instSer q) s = true ↔ ∃ c, q.tnI.label u = Sum.inr c := by
  rw [isComp, lblB_iff q hs]
  simp only [TnDesc.label]
  rcases q.tnI.lbl.lookup u with _ | ⟨b, n⟩
  · simp
  · cases b <;> simp [List.cons_prefix_cons]

theorem cobhamB_lblB (K : List Bool) {x s : Fn} (hx : Cobham x) (hs : Cobham s) :
    CobhamB fun args => lblB K (x args) (s args) :=
  cobhamB_firstLabelS (cobham_const K) (cobham_yE hx) (cobham_nvAt hs)

theorem cobhamB_actIs (a : ℕ) {x s : Fn} (hx : Cobham x) (hs : Cobham s) :
    CobhamB fun args => actIs a (x args) (s args) :=
  (cobhamB_lblB _ hx hs).or ((cobhamB_const _).and (cobhamB_lblB _ hx hs).not)

theorem cobhamB_compIs (c : ℕ) {x s : Fn} (hx : Cobham x) (hs : Cobham s) :
    CobhamB fun args => compIs c (x args) (s args) :=
  cobhamB_lblB _ hx hs

theorem cobhamB_isComp {x s : Fn} (hx : Cobham x) (hs : Cobham s) :
    CobhamB fun args => isComp (x args) (s args) :=
  cobhamB_lblB _ hx hs

end TOPlan

end Syn

end HTN
