import HtnComplexity.Complexity.TOPlan.ReachB
import HtnComplexity.Complexity.TOPlan.Sem
/-!
# The planner for totally ordered instances at a fixed domain, on bit strings

For a fixed domain description `d`, the planner reads the serialisation `x = instSer q` of an
instance description and runs the automaton of `HtnComplexity/Complexity/TOPlan/Sem.lean`
along the initial task network of `q`, linearised on the fly.

* The **configuration** is a bit string `encS d S ++ V`: the current set `S` of projected states
  (one bit per subset of the vocabulary of `d`), followed by one bit per position of `x` marking
  the identifier entries already processed.
* `HTN.Syn.TOPlan.nextB x V s` — the identifier entry at `s` is the **next** one: it is not
  processed, and no unprocessed identifier with another numeral is ordered before it
  (`HTN.Syn.TOPlan.isNextId_iff`: on a totally ordered network this is the next element of the
  linearisation `HTN.Syn.TnDesc.lin`).
* `HTN.Syn.TOPlan.loopStep` — one step: mark the next identifier, and move `S` along its letter
  (up to the finitely many classes of `HTN.Syn.TOPlan.clsOf`).
* `HTN.Syn.TOPlan.planB d x` — initialise, iterate `|x|` times, accept.
* `HTN.Syn.TOPlan.planB_iff` — **correctness**: for a domain with totally ordered methods and a
  totally ordered instance, `planB d (instSer q)` decides `Solvable d q`.
-/

namespace HTN

namespace Syn

namespace TOPlan

open PTime Compress Classical

/-! ### The next element of the linearisation -/

/-- `u` is the **next** identifier after the processed identifiers `P`: it is not processed, and
no other unprocessed identifier is ordered before it. -/
def IsNextId (t : TnDesc) (P : List ℕ) (u : ℕ) : Prop :=
  u ∉ P ∧ ∀ v ∈ t.ids, v ∉ P → v ≠ u → ¬ t.preOrd v u

theorem getElem_mem_take_iff {L : List ℕ} (hnd : L.Nodup) {j k : ℕ} (hj : j < L.length) :
    L[j] ∈ L.take k ↔ j < k := by
  constructor
  · intro h
    obtain ⟨i, hi, hij⟩ := List.mem_iff_getElem.1 h
    rw [List.getElem_take] at hij
    have hi' : i < k := by simp at hi; omega
    have : i = j := (hnd.getElem_inj_iff (hi := by simp at hi; omega) (hj := hj)).1 hij
    omega
  · intro h
    exact List.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩

section LinNext

variable {t : TnDesc}

/-- **The next identifier is the next element of the linearisation.** -/
theorem isNextId_iff (hTO : t.toTaskNetwork.IsTotallyOrdered) {k : ℕ} (hk : k < (TnDesc.lin t).length)
    {u : ℕ} (hu : u ∈ t.ids) : IsNextId t ((TnDesc.lin t).take k) u ↔ u = (TnDesc.lin t)[k] := by
  have hlin := TnDesc.isLinearization_lin hTO
  have hnd := TnDesc.nodup_lin t
  have hpw := List.pairwise_iff_getElem.1 hlin.2.2
  have hmemL : ∀ v, v ∈ TnDesc.lin t ↔ v ∈ t.ids := fun v => TnDesc.mem_lin hTO
  have hTO' : ∀ v ∈ t.ids, ∀ w ∈ t.ids, v ≠ w →
      t.toTaskNetwork.ord v w ∨ t.toTaskNetwork.ord w v :=
    fun v hv w hw hne => hTO v (by simpa using hv) w (by simpa using hw) hne
  have hidx : ∀ v ∈ t.ids, v ∉ (TnDesc.lin t).take k →
      ∃ j, ∃ hj : j < (TnDesc.lin t).length, k ≤ j ∧ (TnDesc.lin t)[j] = v := by
    intro v hv hvP
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ((hmemL v).2 hv)
    refine ⟨j, hj, ?_, rfl⟩
    by_contra h
    exact hvP ((getElem_mem_take_iff hnd hj).2 (by omega))
  have hw : (TnDesc.lin t)[k] ∈ t.ids := (hmemL _).1 (List.getElem_mem hk)
  have hwP : (TnDesc.lin t)[k] ∉ (TnDesc.lin t).take k := fun h => by
    have := (getElem_mem_take_iff hnd hk).1 h
    omega
  constructor
  · rintro ⟨huP, hmin⟩
    by_contra hne
    obtain ⟨j, hj, hkj, rfl⟩ := hidx u hu huP
    have hkj' : k < j := by
      rcases Nat.lt_or_eq_of_le hkj with h | h
      · exact h
      · subst h; exact absurd rfl hne
    have h1 := hmin _ hw hwP (fun h => hne h.symm)
    have h2 := hpw k j hk hj hkj'
    rcases hTO' _ hw _ hu (fun h => hne h.symm) with h | h
    · exact h1 ((TnDesc.toTaskNetwork_ord _ _ _).1 h).2.2.1
    · exact h2 h
  · rintro rfl
    refine ⟨hwP, fun v hv hvP hne hpre => ?_⟩
    obtain ⟨j, hj, hkj, rfl⟩ := hidx v hv hvP
    have hkj' : k < j := by
      rcases Nat.lt_or_eq_of_le hkj with h | h
      · exact h
      · subst h; exact absurd rfl hne
    have h2 := hpw k j hk hj hkj'
    rcases hTO' _ hv _ hw hne with h | h
    · exact h2 h
    · exact ((TnDesc.toTaskNetwork_ord _ _ _).1 h).2.2.2 hpre

/-- After the whole linearisation, nothing is next. -/
theorem not_isNextId (hTO : t.toTaskNetwork.IsTotallyOrdered) {k : ℕ}
    (hk : (TnDesc.lin t).length ≤ k) {u : ℕ} (hu : u ∈ t.ids) : ¬ IsNextId t ((TnDesc.lin t).take k) u := by
  rintro ⟨huP, -⟩
  rw [List.take_of_length_le hk] at huP
  exact huP ((TnDesc.mem_lin hTO).2 hu)

end LinNext

/-! ### The functions -/

variable (d : DomDesc)

/-- The subsets of the vocabulary, listed. -/
noncomputable def subs : List (Finset ℕ) := (vocab d).powerset.toList

/-- The number of subsets of the vocabulary. -/
noncomputable def nS : ℕ := (subs d).length

/-- The `i`-th subset of the vocabulary. -/
noncomputable def sub (i : ℕ) : Finset ℕ := (subs d).getD i ∅

/-- **The encoding of a set of projected states**: one bit per subset of the vocabulary. -/
noncomputable def encS (S : Finset (Finset ℕ)) : List Bool :=
  (List.range (nS d)).map fun i => decide (sub d i ∈ S)

/-- **The identifier entry at `s` is the next one** (`V` marks the processed entries). -/
def nextB (x V s : List Bool) : Bool :=
  idPos x s && !bitAt V x s && x.tails.all fun c =>
    !(idPos x c && !bitAt V x c && !decide (nvAt c = nvAt s) &&
      preOrdB (dbl (nvAt c)) (dbl (nvAt s)) x)

/-- The class test, abstractly: `fA a` — the label is the action `a`; `fC c` — the label is the
compound task `c`; `iC` — the label is compound. -/
def clsG (ℓ : ℕ ⊕ ℕ) (fA fC : ℕ → Bool) (iC : Bool) : Bool :=
  match ℓ with
  | .inl a => if a ∈ anames d then fA a else (!(anames d).any fA && !iC)
  | .inr c => if c ∈ heads d then fC c else (iC && !(heads d).any fC)

/-- **The letter class of the identifier whose entry starts at `s` is `ℓ`.** -/
def clsB (ℓ : ℕ ⊕ ℕ) (x s : List Bool) : Bool :=
  clsG d ℓ (fun a => actIs a x s) (fun c => compIs c x s) (isComp x s)

/-- Some identifier is next. -/
def anyNext (x V : List Bool) : Bool := x.tails.any (nextB x V)

/-- The next identifier has the letter class `ℓ`. -/
def nextCls (ℓ : ℕ ⊕ ℕ) (x V : List Bool) : Bool :=
  x.tails.any fun s => nextB x V s && clsB d ℓ x s

/-- The transition of the automaton between the `i`-th and the `j`-th subset. -/
noncomputable def relB (ℓ : ℕ ⊕ ℕ) (i j : ℕ) : Bool := decide (rel d ℓ (sub d i) (sub d j))

/-- The new set of projected states. -/
noncomputable def snew (x S V : List Bool) : List Bool :=
  (List.range (nS d)).map fun j =>
    (anyNext x V && (letters d).any fun ℓ => nextCls d ℓ x V &&
      (List.range (nS d)).any fun i => bitI S i && relB d ℓ i j) || (!anyNext x V && bitI S j)

/-- The new marking: the next identifier is processed. -/
def vnew (x V : List Bool) : List Bool := x.tails.map fun c => bitAt V x c || nextB x V c

/-- **One step of the planner.** -/
noncomputable def loopStep (x st : List Bool) : List Bool :=
  snew d x (st.take (nS d)) (st.drop (nS d)) ++ vnew x (st.drop (nS d))

/-- The initial configuration. -/
noncomputable def initSt (x : List Bool) : List Bool :=
  (List.range (nS d)).map (fun i => (vocab d).toList.all fun f =>
    decide (f ∈ sub d i) == occB x (true :: serNat f)) ++ x.tails.map fun _ => false

/-- The final configuration. -/
noncomputable def finalSt (x : List Bool) : List Bool := (loopStep d x)^[x.length] (initSt d x)

/-- Acceptance: some state of the final set contains the goal facts of the vocabulary. -/
noncomputable def accB (x st : List Bool) : Bool :=
  (List.range (nS d)).any fun i => bitI st i && (vocab d).toList.all fun f =>
    !occB (yB x) (true :: serNat f) || decide (f ∈ sub d i)

/-- **The planner.** -/
noncomputable def planB (x : List Bool) : Bool :=
  accB d x (finalSt d x) && inclB ((vocab d).toList.map entryEnc) x

variable {d}

/-! ### Subsets -/

theorem sub_mem {i : ℕ} (hi : i < nS d) : sub d i ∈ (vocab d).powerset := by
  rw [sub, List.getD_eq_getElem _ _ hi]
  exact (Finset.mem_toList).1 (List.getElem_mem _)

theorem exists_sub {u : Finset ℕ} (hu : u ∈ (vocab d).powerset) : ∃ i < nS d, sub d i = u := by
  obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.1 ((Finset.mem_toList).2 hu : u ∈ subs d)
  exact ⟨i, hi, by simp only [sub, subs]; rw [List.getD_eq_getElem _ _ hi, h]⟩

@[simp] theorem length_encS (S : Finset (Finset ℕ)) : (encS d S).length = nS d := by simp [encS]

theorem bitI_encS (S : Finset (Finset ℕ)) {i : ℕ} (hi : i < nS d) :
    bitI (encS d S) i = decide (sub d i ∈ S) := by
  rw [encS, bitI_map _ _ (by simpa using hi)]
  simp

theorem serNat_inj {a b : ℕ} : serNat a = serNat b ↔ a = b :=
  ⟨fun h => bitsOfNat_injective (bstr_parse (r := []) (s := []) (by simpa using h)).1,
    fun h => by rw [h]⟩

/-! ### The next identifier on bit strings -/

/-- The marking `V` marks exactly the identifier entries carrying a numeral of `P`. -/
def MarksP (q : InstDesc) (V : List Bool) (P : List ℕ) : Prop :=
  ∀ c, c <:+ instSer q →
    (bitAt V (instSer q) c = true ↔ idPos (instSer q) c = true ∧ ∃ u ∈ P, nvAt c = serNat u)

theorem nextB_iff {q : InstDesc} {V : List Bool} {P : List ℕ} (hV : MarksP q V P)
    {s : List Bool} (hs : s <:+ instSer q) :
    nextB (instSer q) V s = true ↔
      idPos (instSer q) s = true ∧ ∃ u, nvAt s = serNat u ∧ IsNextId q.tnI P u := by
  set x := instSer q with hx
  by_cases hid : idPos x s = true
  swap
  · simp only [Bool.not_eq_true] at hid
    simp [nextB, hid]
  obtain ⟨u, hu, hsu⟩ := idPos_val hid
  have hbit : bitAt V x s = true ↔ u ∈ P := by
    rw [hV s hs, hsu]
    simp only [serNat_inj]
    exact ⟨fun ⟨_, u', hu', h⟩ => by rw [h]; exact hu', fun h => ⟨hid, u, h, rfl⟩⟩
  have hc : ∀ c, c <:+ x → idPos x c = true →
      ∃ v ∈ q.tnI.ids, nvAt c = serNat v ∧ (bitAt V x c = true ↔ v ∈ P) := by
    intro c hcx hcid
    obtain ⟨v, hv, hcv⟩ := idPos_val hcid
    refine ⟨v, hv, hcv, ?_⟩
    rw [hV c hcx, hcv]
    simp only [serNat_inj]
    exact ⟨fun ⟨_, u', hu', h⟩ => by rw [h]; exact hu', fun h => ⟨hcid, v, h, rfl⟩⟩
  have hall : (∀ c, c <:+ x → ¬ (idPos x c = true ∧ bitAt V x c = false ∧ nvAt c ≠ nvAt s ∧
      preOrdB (dbl (nvAt c)) (dbl (nvAt s)) x = true)) ↔
      ∀ v ∈ q.tnI.ids, v ∉ P → v ≠ u → ¬ q.tnI.preOrd v u := by
    rw [hsu]
    constructor
    · intro h v hv hvP hvu hpre
      obtain ⟨c, hcx, hcid, hcv⟩ := exists_idPos_of_mem hv
      obtain ⟨v', hv', hcv', hb⟩ := hc c hcx hcid
      rw [hcv, serNat_inj] at hcv'
      subst hcv'
      refine h c hcx ⟨hcid, ?_, ?_, ?_⟩
      · rw [← Bool.not_eq_true, hb]; exact hvP
      · rw [hcv]; exact fun h => hvu (serNat_inj.1 h)
      · rw [hcv]; exact (preOrdB_iff q v u).2 hpre
    · rintro h c hcx ⟨hcid, hb, hne, hpre⟩
      obtain ⟨v, hv, hcv, hbv⟩ := hc c hcx hcid
      rw [hcv] at hne hpre
      refine h v hv ?_ (fun h => hne (by rw [h])) ((preOrdB_iff q v u).1 hpre)
      intro hvP
      rw [← hbv] at hvP
      rw [hvP] at hb
      exact absurd hb (by simp)
  have hall' : (x.tails.all fun c => !(idPos x c && !bitAt V x c && !decide (nvAt c = nvAt s) &&
      preOrdB (dbl (nvAt c)) (dbl (nvAt s)) x)) = true ↔
      ∀ c, c <:+ x → ¬ (idPos x c = true ∧ bitAt V x c = false ∧ nvAt c ≠ nvAt s ∧
        preOrdB (dbl (nvAt c)) (dbl (nvAt s)) x = true) := by
    simp only [List.all_eq_true, List.mem_tails]
    refine forall_congr' fun c => imp_congr_right fun _ => ?_
    cases idPos x c <;> cases bitAt V x c <;>
      cases preOrdB (dbl (nvAt c)) (dbl (nvAt s)) x <;> by_cases h : nvAt c = nvAt s <;> simp [h]
  have hnb : nextB x V s = true ↔ ¬ bitAt V x s = true ∧ (x.tails.all fun c =>
      !(idPos x c && !bitAt V x c && !decide (nvAt c = nvAt s) &&
        preOrdB (dbl (nvAt c)) (dbl (nvAt s)) x)) = true := by
    simp only [nextB, hid, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true']
    simp
  rw [hnb, hall', hall, hbit]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hid, u, hsu, h1, h2⟩
  · rintro ⟨-, u', hsu', h1, h2⟩
    rw [hsu, serNat_inj] at hsu'
    subst hsu'
    exact ⟨h1, h2⟩

/-- **In the middle of the linearisation** the next entries are those of its `k`-th element. -/
theorem nextB_iff_mid {q : InstDesc} (hq : q.IsTO) {k : ℕ} (hk : k < (TnDesc.lin q.tnI).length)
    {V : List Bool} (hV : MarksP q V ((TnDesc.lin q.tnI).take k)) {s : List Bool}
    (hs : s <:+ instSer q) :
    nextB (instSer q) V s = true ↔
      idPos (instSer q) s = true ∧ nvAt s = serNat (TnDesc.lin q.tnI)[k] := by
  have hw : (TnDesc.lin q.tnI)[k] ∈ q.tnI.ids := (TnDesc.mem_lin hq).1 (List.getElem_mem hk)
  rw [nextB_iff hV hs]
  constructor
  · rintro ⟨hid, u, hsu, hn⟩
    obtain ⟨u', hu', hsu'⟩ := idPos_val hid
    rw [hsu, serNat_inj] at hsu'
    subst hsu'
    exact ⟨hid, by rw [hsu, (isNextId_iff hq hk hu').1 hn]⟩
  · rintro ⟨hid, hsw⟩
    exact ⟨hid, _, hsw, (isNextId_iff hq hk hw).2 rfl⟩

/-- **After the linearisation** nothing is next. -/
theorem nextB_false_end {q : InstDesc} (hq : q.IsTO) {k : ℕ}
    (hk : (TnDesc.lin q.tnI).length ≤ k) {V : List Bool}
    (hV : MarksP q V ((TnDesc.lin q.tnI).take k)) {s : List Bool} (hs : s <:+ instSer q) :
    nextB (instSer q) V s = false := by
  rw [← Bool.not_eq_true, nextB_iff hV hs]
  rintro ⟨hid, u, hsu, hn⟩
  obtain ⟨u', hu', hsu'⟩ := idPos_val hid
  rw [hsu, serNat_inj] at hsu'
  subst hsu'
  exact not_isNextId hq hk hu' hn

/-! ### Letter classes on bit strings -/

theorem clsG_iff {L ℓ : ℕ ⊕ ℕ} {fA fC : ℕ → Bool} {iC : Bool}
    (hA : ∀ a, fA a = true ↔ L = Sum.inl a) (hC : ∀ c, fC c = true ↔ L = Sum.inr c)
    (hI : iC = true ↔ ∃ c, L = Sum.inr c) (hℓ : ℓ ∈ letters d) :
    clsG d ℓ fA fC iC = true ↔ clsOf d L = ℓ := by
  have hfa := freshA_nmem d
  have hfc := freshC_nmem d
  rcases ℓ with a | c
  · have hℓ' : a ∈ anames d ∨ a = freshA d := by simpa [letters] using hℓ
    simp only [clsG]
    split_ifs with ha
    · rw [hA]
      rcases L with a0 | c0
      · simp only [clsOf]
        split_ifs with ha0
        · simp
        · simp only [Sum.inl.injEq]
          constructor
          · rintro rfl; exact absurd ha ha0
          · rintro rfl; exact absurd ha hfa
      · simp [clsOf]; split_ifs <;> simp
    · have haf : a = freshA d := hℓ'.resolve_left ha
      subst haf
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hI,
        List.any_eq_true, hA, not_exists, not_and]
      rcases L with a0 | c0
      · simp only [clsOf, reduceCtorEq, not_false_eq_true]
        split_ifs with ha0
        · simp only [Sum.inl.injEq]
          constructor
          · intro h; exact absurd rfl (h.1 a0 ha0)
          · rintro rfl; exact absurd ha0 hfa
        · simp only [iff_true]
          refine ⟨fun a' ha' h => ha0 ?_, fun _ => trivial⟩
          cases h; exact ha'
      · simp [clsOf]; split_ifs <;> simp
  · have hℓ' : c ∈ heads d ∨ c = freshC d := by simpa [letters] using hℓ
    simp only [clsG]
    split_ifs with hc
    · rw [hC]
      rcases L with a0 | c0
      · simp [clsOf]; split_ifs <;> simp
      · simp only [clsOf]
        split_ifs with hc0
        · simp
        · simp only [Sum.inr.injEq]
          constructor
          · rintro rfl; exact absurd hc hc0
          · rintro rfl; exact absurd hc hfc
    · have hcf : c = freshC d := hℓ'.resolve_left hc
      subst hcf
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hI,
        List.any_eq_true, hC, not_exists, not_and]
      rcases L with a0 | c0
      · simp [clsOf]; split_ifs <;> simp
      · simp only [clsOf, Sum.inr.injEq, exists_eq', true_and]
        split_ifs with hc0
        · simp only [Sum.inr.injEq]
          constructor
          · intro h; exact absurd rfl (h c0 hc0)
          · rintro rfl; exact absurd hc0 hfc
        · simp only [iff_true]
          exact fun c' hc' h => hc0 (h ▸ hc')

/-- **The class test reads the letter class of the label.** -/
theorem clsB_iff (q : InstDesc) {s : List Bool} {u : ℕ} (hs : nvAt s = serNat u)
    {ℓ : ℕ ⊕ ℕ} (hℓ : ℓ ∈ letters d) :
    clsB d ℓ (instSer q) s = true ↔ clsOf d (q.tnI.label u) = ℓ :=
  clsG_iff (fun a => actIs_iff q hs a) (fun c => compIs_iff q hs c) (isComp_iff q hs) hℓ

/-! ### The invariant of the loop -/

variable (d) in
/-- **The configuration after `k` steps**: the set of projected states reached along the first
`k` letters of the linearisation, and the marking of the identifiers among its first `k`
elements. -/
def Conf (q : InstDesc) (k : ℕ) (st : List Bool) : Prop :=
  ∃ V, st = encS d (run d {initProj d q} (((TnDesc.lin q.tnI).take k).map q.tnI.label)) ++ V ∧
    V.length = (instSer q).length + 1 ∧ MarksP q V ((TnDesc.lin q.tnI).take k)

theorem run_append_single (S : Finset (Finset ℕ)) (xs : List (ℕ ⊕ ℕ)) (y : ℕ ⊕ ℕ) :
    run d S (xs ++ [y]) = step d (run d S xs) y := by
  simp [run, List.foldl_append]

theorem singleton_initProj_subset (q : InstDesc) :
    ({initProj d q} : Finset (Finset ℕ)) ⊆ (vocab d).powerset := by
  intro s hs
  rw [Finset.mem_singleton.1 hs, Finset.mem_powerset]
  exact Finset.filter_subset _ _

theorem snew_mid {q : InstDesc} {S : Finset (Finset ℕ)} (hS : S ⊆ (vocab d).powerset)
    {V : List Bool} {w : ℕ} (hany : anyNext (instSer q) V = true)
    (hcls : ∀ ℓ ∈ letters d, nextCls d ℓ (instSer q) V = true ↔ clsOf d (q.tnI.label w) = ℓ) :
    snew d (instSer q) (encS d S) V = encS d (step d S (q.tnI.label w)) := by
  unfold snew
  conv_rhs => rw [encS]
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < nS d := List.mem_range.1 hj
  rw [hany]
  simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, Bool.and_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨ℓ, hℓ, hc, i, hi, hb, hr⟩
    rw [hcls ℓ hℓ] at hc
    subst hc
    rw [bitI_encS _ hi, decide_eq_true_eq] at hb
    rw [relB, decide_eq_true_eq] at hr
    rw [← step_clsOf]
    simp only [step, Finset.mem_filter]
    exact ⟨sub_mem hj', sub d i, hb, hr⟩
  · intro h
    rw [← step_clsOf] at h
    simp only [step, Finset.mem_filter] at h
    obtain ⟨-, s0, hs0, hr⟩ := h
    obtain ⟨i, hi, rfl⟩ := exists_sub (hS hs0)
    refine ⟨_, clsOf_mem_letters _, (hcls _ (clsOf_mem_letters _)).2 rfl, i, hi, ?_, ?_⟩
    · rw [bitI_encS _ hi]; simpa using hs0
    · rw [relB]; simpa using hr

theorem snew_end {x V : List Bool} {S : Finset (Finset ℕ)} (hany : anyNext x V = false) :
    snew d x (encS d S) V = encS d S := by
  unfold snew
  conv_rhs => rw [encS]
  refine List.map_congr_left fun j hj => ?_
  rw [hany, bitI_encS _ (List.mem_range.1 hj)]
  simp

/-- **One step of the loop keeps the invariant.** -/
theorem conf_loopStep {q : InstDesc} (hq : q.IsTO) {k : ℕ} {st : List Bool}
    (h : Conf d q k st) : Conf d q (k + 1) (loopStep d (instSer q) st) := by
  obtain ⟨V, rfl, hVl, hV⟩ := h
  set S := run d {initProj d q} (((TnDesc.lin q.tnI).take k).map q.tnI.label) with hSdef
  have hS : S ⊆ (vocab d).powerset := run_subset (singleton_initProj_subset q) _
  have htake : (encS d S ++ V).take (nS d) = encS d S := List.take_left' (by simp)
  have hdrop : (encS d S ++ V).drop (nS d) = V := List.drop_left' (by simp)
  simp only [loopStep, htake, hdrop]
  by_cases hk : k < (TnDesc.lin q.tnI).length
  · set w := (TnDesc.lin q.tnI)[k] with hwdef
    have hw : w ∈ q.tnI.ids := (TnDesc.mem_lin hq).1 (List.getElem_mem hk)
    have hnext := fun s (hs : s <:+ instSer q) => nextB_iff_mid hq hk hV hs
    have hany : anyNext (instSer q) V = true := by
      obtain ⟨s, hs, hid, hsw⟩ := exists_idPos_of_mem hw
      exact List.any_eq_true.2 ⟨s, (List.mem_tails _ _).2 hs, (hnext s hs).2 ⟨hid, hsw⟩⟩
    have hcls : ∀ ℓ ∈ letters d,
        nextCls d ℓ (instSer q) V = true ↔ clsOf d (q.tnI.label w) = ℓ := by
      intro ℓ hℓ
      simp only [nextCls, List.any_eq_true, List.mem_tails, Bool.and_eq_true]
      constructor
      · rintro ⟨s, hs, hn, hc⟩
        obtain ⟨-, hsw⟩ := (hnext s hs).1 hn
        exact (clsB_iff q hsw hℓ).1 hc
      · intro hc
        obtain ⟨s, hs, hid, hsw⟩ := exists_idPos_of_mem hw
        exact ⟨s, hs, (hnext s hs).2 ⟨hid, hsw⟩, (clsB_iff q hsw hℓ).2 hc⟩
    have htk : (TnDesc.lin q.tnI).take (k + 1) = (TnDesc.lin q.tnI).take k ++ [w] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      rfl
    refine ⟨vnew (instSer q) V, ?_, by simp [vnew], ?_⟩
    · rw [snew_mid hS hany hcls, htk, List.map_append, List.map_singleton, run_append_single]
    · intro c hc
      rw [vnew, bitAt_map_tails _ hc, Bool.or_eq_true, hV c hc, hnext c hc, htk]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (⟨h1, u, hu, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, u, Or.inl hu, h2⟩
        · exact ⟨h1, w, Or.inr rfl, h2⟩
      · rintro ⟨h1, u, hu | rfl, h2⟩
        · exact Or.inl ⟨h1, u, hu, h2⟩
        · exact Or.inr ⟨h1, h2⟩
  · have hk' : (TnDesc.lin q.tnI).length ≤ k := by omega
    have hnext := fun s (hs : s <:+ instSer q) => nextB_false_end hq hk' hV hs
    have hany : anyNext (instSer q) V = false := by
      rw [anyNext, ← Bool.not_eq_true, List.any_eq_true]
      rintro ⟨s, hs, h⟩
      rw [hnext s ((List.mem_tails _ _).1 hs)] at h
      exact absurd h (by simp)
    have htk : (TnDesc.lin q.tnI).take (k + 1) = (TnDesc.lin q.tnI).take k := by
      rw [List.take_of_length_le hk', List.take_of_length_le (by omega)]
    refine ⟨vnew (instSer q) V, ?_, by simp [vnew], ?_⟩
    · rw [snew_end hany, htk]
    · intro c hc
      rw [vnew, bitAt_map_tails _ hc, hnext c hc, Bool.or_false, htk]
      exact hV c hc

/-! ### Initialisation, iteration, acceptance -/

theorem occB_init_iff (q : InstDesc) (f : ℕ) :
    occB (instSer q) (true :: serNat f) = true ↔ f ∈ q.initList := by
  rw [instSer_eq, serNat, occB_iff]
  simp [bitsOfNat_injective.eq_iff]

theorem occB_goal_iff (q : InstDesc) (f : ℕ) :
    occB (yB (instSer q)) (true :: serNat f) = true ↔ f ∈ q.goalList := by
  rw [yB_instSer, zB, serNat, occB_iff]
  simp [bitsOfNat_injective.eq_iff]

theorem conf_init (q : InstDesc) : Conf d q 0 (initSt d (instSer q)) := by
  refine ⟨(instSer q).tails.map fun _ => false, ?_, by simp, ?_⟩
  · simp only [List.take_zero, List.map_nil, run, List.foldl_nil, initSt, encS]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < nS d := List.mem_range.1 hi
    have hf : ∀ f, (decide (f ∈ sub d i) == occB (instSer q) (true :: serNat f)) = true ↔
        (f ∈ sub d i ↔ f ∈ q.initList) := by
      intro f
      rw [← occB_init_iff q f]
      cases occB (instSer q) (true :: serNat f) <;> simp
    rw [Bool.eq_iff_iff, List.all_eq_true]
    simp only [Finset.mem_toList, hf, decide_eq_true_eq, Finset.mem_singleton]
    have hsub := Finset.mem_powerset.1 (sub_mem hi')
    constructor
    · intro h
      ext f
      simp only [initProj, Finset.mem_filter]
      by_cases hfv : f ∈ vocab d
      · rw [h f hfv]; simp [hfv]
      · simp only [hfv, false_and, iff_false]
        exact fun hf => hfv (hsub hf)
    · intro h f hfv
      rw [h]
      simp [initProj, hfv]
  · intro c hc
    rw [bitAt_map_tails _ hc]
    simp

theorem conf_iterate {q : InstDesc} (hq : q.IsTO) :
    ∀ n, Conf d q n ((loopStep d (instSer q))^[n] (initSt d (instSer q)))
  | 0 => conf_init q
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact conf_loopStep hq (conf_iterate hq n)

theorem length_lin_le_instSer (q : InstDesc) :
    (TnDesc.lin q.tnI).length ≤ (instSer q).length := by
  have h1 := TnDesc.length_lin_le q.tnI
  have h2 : (zC q).length ≤ (instSer q).length := (zC_suffix q).length_le
  have h3 : (zC q).length = (blist (q.tnI.ids.map bitsOfNat)).length + (zD q).length := by
    simp [zC]
  have h4 := length_blist (q.tnI.ids.map bitsOfNat)
  have h5 : ∀ l : List ℕ, l.length ≤ ((l.map bitsOfNat).map fun x => 2 * x.length + 2).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
  have := h5 q.tnI.ids
  omega

theorem accB_iff (q : InstDesc) {S : Finset (Finset ℕ)} (hS : S ⊆ (vocab d).powerset)
    (V : List Bool) : accB d (instSer q) (encS d S ++ V) = true ↔ Accepts d q S := by
  simp only [accB, List.any_eq_true, List.mem_range, Bool.and_eq_true, List.all_eq_true,
    Finset.mem_toList, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hb, hg⟩
    rw [bitI_append_left (by simpa using hi), bitI_encS _ hi, decide_eq_true_eq] at hb
    refine ⟨sub d i, hb, fun f hfv hfg => ?_⟩
    rcases hg f hfv with h | h
    · rw [← Bool.not_eq_true, occB_goal_iff] at h
      exact absurd hfg h
    · exact h
  · rintro ⟨u, hu, hg⟩
    obtain ⟨i, hi, rfl⟩ := exists_sub (hS hu)
    refine ⟨i, hi, ?_, fun f hfv => ?_⟩
    · rw [bitI_append_left (by simpa using hi), bitI_encS _ hi, decide_eq_true_eq]
      exact hu
    · by_cases hfg : f ∈ q.goalList
      · exact Or.inr (hg f hfv hfg)
      · left
        rw [← Bool.not_eq_true, occB_goal_iff]
        exact hfg

/-- **Correctness of the planner**: for a domain description with totally ordered methods and a
totally ordered instance description, the planner decides plan existence. -/
theorem planB_iff (hTO : d.MethodsTO) {q : InstDesc} (hq : q.IsTO) :
    planB d (instSer q) = true ↔ Solvable d q := by
  obtain ⟨V, hst, -, -⟩ := conf_iterate (d := d) hq (instSer q).length
  rw [solvable_iff_run hTO hq, planB, finalSt, hst, Bool.and_eq_true,
    List.take_of_length_le (length_lin_le_instSer q),
    accB_iff q (run_subset (singleton_initProj_subset q) _), inclB_iff]
  simp only [Finset.mem_toList]
  rfl

end TOPlan

end Syn

end HTN
