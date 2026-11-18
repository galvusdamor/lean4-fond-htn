import FondHtn.AcycHard.InstHier
import FondHtn.HardMP.Sem
import FondHtn.HardMP.Classes
import FondHtn.AcycHard.Transfer
/-!
# The description of the Savitch instance

`FOND.AcycHard.Sav.Inst.desc`: the FOND problem description of an instance.

* Actions: the control instructions (`ctlLists`), the refill (adds the preconditions of all pool
  actions) and the pool actions (`poolLists`), over the coded facts `codeTok`.
* Methods: one per compound name of `cnList`, a sequence network (`seqTn`) for seq-kind and a
  set network (`setTn`, no order) for set-kind names.
* Initial task network: the unordered roots `ctl` and `pool`; initial state `st (inp 0)`.

Validity, `Fit` with the hierarchy specification `Inst.hs`, the closure of the reachable names,
the invariant of the initial network and acyclicity.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

namespace Sav

open HTN HTN.Syn HTN.Article TM HardMP

variable {k : ℕ}

/-! ## Set networks -/

/-- **The set network** of a list of labels: no order. -/
def setTn (ls : List (Bool × ℕ)) : TnDesc :=
  (List.range ls.length, [], (List.range ls.length).map fun i => (i, ls.getI i))

theorem setTn_label (ls : List (Bool × ℕ)) : (setTn ls).label = (seqTn ls).label := rfl

theorem setTn_T (ls : List (Bool × ℕ)) : (setTn ls).toTaskNetwork.T = (seqTn ls).toTaskNetwork.T := rfl

theorem setTn_valid {prim : ℕ → Prop} {ls : List (Bool × ℕ)}
    (hprim : ∀ q ∈ ls, q.1 = false → prim q.2) : TnValid prim (setTn ls) := by
  have h := seqTn_valid hprim
  exact ⟨h.nodup, by simp [setTn, TnDesc.ordList], by simp [setTn, TnDesc.ordList],
    by simp [setTn, TnDesc.ordList], h.lbl_perm, h.prim_ok⟩

theorem setTn_not_ord (ls : List (Bool × ℕ)) (a b : ℕ) : ¬ (setTn ls).toTaskNetwork.ord a b := by
  rintro ⟨-, -, h, -⟩
  induction h with
  | single h => simp [TnDesc.listRel, setTn, TnDesc.ordList] at h
  | tail _ h _ => simp [TnDesc.listRel, setTn, TnDesc.ordList] at h

theorem setNet_setTn (ls : List (Bool × ℕ)) :
    SetNet (setTn ls).toTaskNetwork (List.range ls.length) (ls.map toLab) where
  nodup := List.nodup_range
  memT x := by simp [TnDesc.toTaskNetwork, setTn, TnDesc.ids]
  labels := map_label_range_seqTn ls
  ord := setTn_not_ord ls

/-- Labels of items. -/
def toLabB : ℕ ⊕ ℕ → Bool × ℕ
  | .inl a => (false, a)
  | .inr c => (true, c)

theorem toLab_toLabB (x : ℕ ⊕ ℕ) : toLab (toLabB x) = x := by cases x <;> rfl

theorem map_toLab_toLabB (l : List (ℕ ⊕ ℕ)) : (l.map toLabB).map toLab = l := by
  simp [List.map_map, Function.comp_def, toLab_toLabB]

/-! ## The lists of names -/

def blks : List Blk := [.WT, .WR, .PRE, .STEP, .ROUND, .REF, .TR]

theorem mem_blks (b : Blk) : b ∈ blks := by cases b <;> simp [blks]

def gates : List Gate := [.T, .R, .F, .I, .U]

theorem mem_gates (g : Gate) : g ∈ gates := by cases g <;> simp [gates]

def pls : List Pl := [.toRd, .half, .halfChk, .acc]

theorem mem_pls (p : Pl) : p ∈ pls := by cases p <;> simp [pls]

/-- The control instructions other than the refill. -/
def ciList : List (CI Gate Pl) := gates.flatMap (fun g => [.opn g, .cls g]) ++ pls.map .plain

theorem mem_ciList (x : CI Gate Pl) (hx : x ≠ .refill) : x ∈ ciList := by
  cases x with
  | opn g => simp [ciList, mem_gates]
  | cls g => simp [ciList, mem_gates]
  | plain p => simp [ciList, mem_pls]
  | refill => exact absurd rfl hx

theorem refill_not_mem_ciList : (CI.refill : CI Gate Pl) ∉ ciList := by simp [ciList]

namespace Inst

variable (I : Inst k)

/-- The pool chain kinds. -/
def sbs : List (SB k) := .blank :: I.syms.map .fresh ++ I.opts.map .opt

/-- **The compound names with a method.** -/
def cnList : List (CN k) :=
  blks.flatMap (fun b => (List.range I.B).map (CN.pw b) ++ [CN.pown b]) ++
    (CN.cellB :: I.syms.map CN.newc) ++
    (CN.ctl :: I.sbs.flatMap (fun s => (List.range I.B).map (CN.spw s) ++ [CN.spown s])) ++ [CN.pool]

theorem mem_cnList_pw {b : Blk} {j : ℕ} (hj : j < I.B) : CN.pw b j ∈ I.cnList := by
  simp [cnList, mem_blks, hj]

theorem mem_cnList_pown (b : Blk) : CN.pown b ∈ I.cnList := by
  simp [cnList, mem_blks]

theorem mem_cnList_spw {s : SB k} (hs : s ∈ I.sbs) {j : ℕ} (hj : j < I.B) : CN.spw s j ∈ I.cnList := by
  simp only [cnList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr (Or.inr ⟨s, hs, Or.inl ⟨j, hj, rfl⟩⟩))

theorem mem_cnList_spown {s : SB k} (hs : s ∈ I.sbs) : CN.spown s ∈ I.cnList := by
  simp only [cnList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr (Or.inr ⟨s, hs, Or.inr (by simp)⟩))

theorem mem_cnList_cellB : CN.cellB ∈ I.cnList := by simp [cnList]

theorem mem_cnList_newc {τ : SymK k} (h : τ ∈ I.syms) : CN.newc τ ∈ I.cnList := by
  simp [cnList, h]

theorem mem_cnList_ctl : CN.ctl ∈ I.cnList := by simp [cnList]

theorem mem_cnList_pool : CN.pool ∈ I.cnList := by simp [cnList]

/-- The compound names of `cnList`. -/
theorem mem_cnList {x : CN k} (h : x ∈ I.cnList) :
    (∃ b j, j < I.B ∧ x = .pw b j) ∨ (∃ b, x = .pown b) ∨ x = .cellB ∨ (∃ τ ∈ I.syms, x = .newc τ) ∨
      x = .ctl ∨ (∃ s ∈ I.sbs, ∃ j, j < I.B ∧ x = .spw s j) ∨ (∃ s ∈ I.sbs, x = .spown s) ∨
      x = .pool := by
  simp only [cnList, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with (((⟨b, -, ⟨j, hj, rfl⟩ | rfl⟩ | rfl | ⟨τ, hτ, rfl⟩) | rfl | ⟨s, hs, ⟨j, hj, rfl⟩ | rfl⟩) | rfl)
  · exact Or.inl ⟨b, j, hj, rfl⟩
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨τ, hτ, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, j, hj, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem blkItems_closed (b : Blk) {y : CN k} (h : Sum.inr y ∈ blkItems (k := k) b) : y ∈ I.cnList := by
  cases b <;> simp [blkItems] at h <;> rcases h with rfl | rfl <;> exact I.mem_cnList_pown _

/-- **The names with a method are closed under the bodies.** -/
theorem body_closed {x y : CN k} (hx : x ∈ I.cnList) (hy : Sum.inr y ∈ I.bodyCN x) : y ∈ I.cnList := by
  rcases I.mem_cnList hx with ⟨b, j, hj, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨τ, hτ, rfl⟩ | rfl |
    ⟨s, hs, j, hj, rfl⟩ | ⟨s, hs, rfl⟩ | rfl
  · cases j with
    | zero => exact I.blkItems_closed b hy
    | succ j =>
      simp only [bodyCN, List.mem_cons, Sum.inr.injEq, List.not_mem_nil, or_false, or_self] at hy
      subst hy; exact I.mem_cnList_pw (by omega)
  · simp only [bodyCN, List.mem_map, List.mem_filter, List.mem_range, Sum.inr.injEq] at hy
    obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hy
    exact I.mem_cnList_pw hj
  · simp only [bodyCN, List.mem_cons, reduceCtorEq, Sum.inr.injEq, List.not_mem_nil, or_false,
      false_or] at hy
    subst hy; exact I.mem_cnList_pown _
  · simp only [bodyCN, List.mem_cons, reduceCtorEq, Sum.inr.injEq, List.not_mem_nil, or_false,
      false_or] at hy
    subst hy; exact I.mem_cnList_pown _
  · simp only [bodyCN, List.mem_cons, reduceCtorEq, Sum.inr.injEq, List.not_mem_nil, or_false,
      false_or] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> exact I.mem_cnList_pown _
  · cases j with
    | zero =>
      simp only [bodyCN, List.mem_singleton] at hy
      cases s with
      | blank => cases hy; exact I.mem_cnList_cellB
      | fresh τ =>
        cases hy
        simp only [sbs, List.mem_cons, reduceCtorEq, List.mem_append, List.mem_map, SB.fresh.injEq,
          exists_eq_right, false_or] at hs
        rcases hs with hs | ⟨o, -, ho⟩
        · exact I.mem_cnList_newc hs
        · cases ho
      | opt o => cases hy
    | succ j =>
      simp only [bodyCN, List.mem_cons, Sum.inr.injEq, List.not_mem_nil, or_false, or_self] at hy
      subst hy; exact I.mem_cnList_spw hs (by omega)
  · simp only [bodyCN, List.mem_map, List.mem_filter, List.mem_range, Sum.inr.injEq] at hy
    obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hy
    exact I.mem_cnList_spw hs hj
  · simp only [bodyCN, List.mem_append, List.mem_cons, List.mem_map, Sum.inr.injEq] at hy
    rcases hy with (rfl | ⟨τ, hτ, rfl⟩) | ⟨o, ho, rfl⟩
    · exact I.mem_cnList_spown (by simp [sbs])
    · exact I.mem_cnList_spown (by simp [sbs, hτ])
    · exact I.mem_cnList_spown (by simp [sbs, ho])

/-! ## The description -/

/-- The labels of the body of a name. -/
def labs (x : CN k) : List (Bool × ℕ) := ((I.bodyCN x).map itemCode).map toLabB

/-- **The method of a name.** -/
def methOf (x : CN k) : MethodDesc :=
  (codeCN x, if isSetCN x then setTn (I.labs x) else seqTn (I.labs x))

/-- Coded facts. -/
def encL (l : List (Tok Gate (DK k))) : List ℕ := l.map codeTok

/-- An action from lists of facts. -/
def actOf (nm : ℕ) (p : List (Tok Gate (DK k)) × List (List (Tok Gate (DK k)) × List (Tok Gate (DK k)))) :
    FActDesc :=
  (nm, encL p.1, [], p.2.map fun e => (encL e.1, encL e.2))

/-- The preconditions of all pool actions. -/
def fullL : List (Tok Gate (DK k)) :=
  gates.map .op ++ I.opts.flatMap fun o => [.dat (.st o.1), .dat (.rd o.2.1), .dat (.wr o.2.2.1)]

/-- The pool actions. -/
def paList : List (PA (SymK k) (OK k)) :=
  I.syms.flatMap (fun τ => [.init τ, .fin τ]) ++ [.tick, .res] ++ I.opts.map .opt

/-- The refill: adds the preconditions of all pool actions. -/
def refillAct : FActDesc := (nC .refill, [], [], [(encL I.fullL, [])])

/-- **The actions.** -/
def acts : List FActDesc :=
  (ciList.map (fun x => actOf (k := k) (nC x) (ctlLists (k := k) I.L x)) ++ [I.refillAct] ++
    I.paList.map (fun a => actOf (nP a) (poolLists a))).dedup

/-- The initial facts. -/
def initL : List ℕ := [codeTok (k := k) (.dat (.st (.inp 0)))]

/-- The initial task network. -/
def tnIL : List (Bool × ℕ) := [(true, codeCN (k := k) .ctl), (true, codeCN (k := k) .pool)]

/-- **The description.** -/
def desc : FProbDesc := ((I.acts, I.cnList.map I.methOf), (initL (k := k), setTn (tnIL (k := k))))

end Inst

/-! ## Names of the actions -/

theorem codePl_inj : Function.Injective codePl := by
  intro a b h; cases a <;> cases b <;> simp_all [codePl]

theorem nC_inj : Function.Injective nC := by
  intro a b h
  rcases a with g | g | p | _ <;> rcases b with g' | g' | p' | _ <;>
    simp only [nC, Nat.pair_eq_pair] at h <;> (try omega)
  · rw [codeGate_inj h.2]
  · rw [codeGate_inj h.2]
  · rw [codePl_inj h.2]
  · rfl

theorem nC_ne_nP (x : CI Gate Pl) (a : PA (SymK k) (OK k)) : nC x ≠ nP a := by
  intro h
  rcases x with g | g | p | _ <;> rcases a with τ | _ | _ | τ | o <;>
    simp only [nC, nP, Nat.pair_eq_pair] at h <;> omega

namespace Inst

variable (I : Inst k)

theorem methods_desc : I.desc.methods = I.cnList.map I.methOf := by simp only [desc, FProbDesc.methods]
theorem actions_desc : I.desc.actions = I.acts := by simp only [desc, FProbDesc.actions]

theorem mem_acts {a : FActDesc} : a ∈ I.acts ↔ (∃ x ∈ ciList, a = actOf (nC x) (ctlLists (k := k) I.L x)) ∨
    a = I.refillAct ∨ ∃ p ∈ I.paList, a = actOf (nP p) (poolLists p) := by
  simp only [acts, List.mem_dedup, List.mem_append, List.mem_map, List.mem_singleton]
  constructor
  · rintro ((⟨x, hx, rfl⟩ | rfl) | ⟨p, hp, rfl⟩)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨p, hp, rfl⟩)
  · rintro (⟨x, hx, rfl⟩ | rfl | ⟨p, hp, rfl⟩)
    · exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨p, hp, rfl⟩

theorem name_actOf (nm : ℕ) (p) : FActDesc.name (actOf (k := k) nm p) = nm := rfl

/-- The name determines the action. -/
theorem acts_name_inj {a b : FActDesc} (ha : a ∈ I.acts) (hb : b ∈ I.acts) (h : a.name = b.name) :
    a = b := by
  rw [mem_acts] at ha hb
  rcases ha with ⟨x, hx, rfl⟩ | rfl | ⟨p, -, rfl⟩ <;> rcases hb with ⟨y, hy, rfl⟩ | rfl | ⟨q, -, rfl⟩ <;>
    simp only [refillAct, FActDesc.name, actOf] at h
  · rw [nC_inj h]
  · exact absurd (nC_inj h ▸ hx) refill_not_mem_ciList
  · exact absurd h (nC_ne_nP _ _)
  · exact absurd (nC_inj h ▸ hy) refill_not_mem_ciList
  · rfl
  · exact absurd h (nC_ne_nP _ _)
  · exact absurd h.symm (nC_ne_nP _ _)
  · exact absurd h.symm (nC_ne_nP _ _)
  · rw [nP_inj h]

theorem acts_nodup : I.acts.Nodup := by unfold acts; exact List.nodup_dedup _

theorem names_nodup : (I.acts.map FActDesc.name).Nodup :=
  I.acts_nodup.map_on fun a ha b hb h => I.acts_name_inj ha hb h

theorem effs_ne (a : FActDesc) (ha : a ∈ I.acts) : a.effs ≠ [] := by
  rw [mem_acts] at ha
  rcases ha with ⟨x, hx, rfl⟩ | rfl | ⟨p, -, rfl⟩
  · rcases x with g | g | p | _
    · simp [actOf, FActDesc.effs, ctlLists]
    · simp [actOf, FActDesc.effs, ctlLists]
    · cases p <;> simp [actOf, FActDesc.effs, ctlLists, peL]
    · exact absurd hx refill_not_mem_ciList
  · simp [refillAct, FActDesc.effs]
  · cases p <;> simp [actOf, FActDesc.effs, poolLists]

theorem declared_nC (x : CI Gate Pl) : I.desc.Declared (nC x) := by
  unfold FProbDesc.Declared
  rw [actions_desc, List.mem_map]
  by_cases hx : x = .refill
  · subst hx; exact ⟨I.refillAct, I.mem_acts.2 (Or.inr (Or.inl rfl)), rfl⟩
  · exact ⟨_, I.mem_acts.2 (Or.inl ⟨x, mem_ciList x hx, rfl⟩), rfl⟩

theorem declared_nP {p : PA (SymK k) (OK k)} (hp : p ∈ I.paList) : I.desc.Declared (nP p) := by
  unfold FProbDesc.Declared
  rw [actions_desc, List.mem_map]
  exact ⟨_, I.mem_acts.2 (Or.inr (Or.inr ⟨p, hp, rfl⟩)), rfl⟩

theorem blkItems_inl (b : Blk) {a : ℕ} (h : Sum.inl a ∈ blkItems (k := k) b) : I.desc.Declared a := by
  cases b <;> simp only [blkItems, List.mem_cons, Sum.inl.injEq, reduceCtorEq, List.not_mem_nil,
    or_false, false_or] at h <;>
    (try rcases h with rfl | rfl | rfl | rfl | rfl | rfl) <;>
    first
    | exact I.declared_nC _
    | exact I.declared_nP (by simp [paList])

/-- **The primitive items of the bodies are declared.** -/
theorem body_inl (hnone : none ∈ I.syms) {x : CN k} (hx : x ∈ I.cnList) {a : ℕ}
    (ha : Sum.inl a ∈ I.bodyCN x) : I.desc.Declared a := by
  rcases I.mem_cnList hx with ⟨b, j, hj, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨τ, hτ, rfl⟩ | rfl |
    ⟨s, hs, j, hj, rfl⟩ | ⟨s, hs, rfl⟩ | rfl
  · cases j with
    | zero => exact I.blkItems_inl b ha
    | succ j => simp [bodyCN] at ha
  · simp [bodyCN] at ha
  · simp only [bodyCN, List.mem_cons, reduceCtorEq, Sum.inl.injEq, List.not_mem_nil, or_false,
      false_or] at ha
    subst ha; exact I.declared_nP (by simp [paList, hnone])
  · simp only [bodyCN, List.mem_cons, reduceCtorEq, Sum.inl.injEq, List.not_mem_nil, or_false,
      false_or] at ha
    rcases ha with rfl | rfl
    · exact I.declared_nP (by simp [paList, hτ])
    · exact I.declared_nP (by simp [paList, hτ])
  · simp only [bodyCN, List.mem_cons, reduceCtorEq, Sum.inl.injEq, List.not_mem_nil, or_false,
      false_or] at ha
    rcases ha with rfl | rfl | rfl <;> exact I.declared_nC _
  · cases j with
    | zero =>
      simp only [bodyCN, List.mem_singleton] at ha
      cases s with
      | blank => cases ha
      | fresh τ => cases ha
      | opt o =>
        simp only [sbItem, Sum.inl.injEq] at ha
        subst ha
        simp only [sbs, List.mem_cons, reduceCtorEq, List.mem_append, List.mem_map, SB.opt.injEq,
          exists_eq_right, false_or] at hs
        rcases hs with ⟨τ, -, h⟩ | hs
        · cases h
        · exact I.declared_nP (by simp [paList, hs])
    | succ j => simp [bodyCN] at ha
  · simp [bodyCN] at ha
  · simp [bodyCN] at ha

theorem labs_prim (hnone : none ∈ I.syms) {x : CN k} (hx : x ∈ I.cnList) :
    ∀ q ∈ I.labs x, q.1 = false → I.desc.Declared q.2 := by
  intro q hq hf
  simp only [labs, List.map_map, List.mem_map, Function.comp_apply] at hq
  obtain ⟨y, hy, rfl⟩ := hq
  rcases y with a | y
  · exact I.body_inl hnone hx hy
  · simp [itemCode, toLabB] at hf

/-- **The description is well formed.** -/
theorem valid (hnone : none ∈ I.syms) : I.desc.Valid where
  names_nodup := by rw [actions_desc]; exact I.names_nodup
  effs_ne := by rw [actions_desc]; exact I.effs_ne
  tnI := setTn_valid (by simp [tnIL])
  methods := by
    intro m hm
    rw [methods_desc, List.mem_map] at hm
    obtain ⟨x, hx, rfl⟩ := hm
    unfold methOf
    split
    · exact setTn_valid (I.labs_prim hnone hx)
    · exact seqTn_valid (I.labs_prim hnone hx)

/-! ## The hierarchy -/

theorem map_labs (x : CN k) : (I.labs x).map toLab = I.hs.body (codeCN x) := by
  rw [labs, map_toLab_toLabB, hs_body]

theorem mem_methods {m : Method ℕ ℕ ℕ} : m ∈ I.desc.toProblem.methods ↔
    ∃ x ∈ I.cnList, (I.methOf x).toMethod = m := by
  simp only [FProbDesc.toProblem, Set.mem_setOf_eq, methods_desc, List.mem_map]
  constructor
  · rintro ⟨e, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- **The methods realise the hierarchy specification.** -/
theorem fit : Fit I.desc.toProblem I.hs := by
  intro m hm
  obtain ⟨x, -, rfl⟩ := I.mem_methods.1 hm
  refine ⟨TnDesc.toTaskNetwork_wf _, fun hs => ?_, fun hs => ?_⟩
  · simp only [MethodDesc.toMethod, methOf, hs_isSet] at hs ⊢
    rw [if_pos hs, ← I.map_labs]
    exact ⟨_, setNet_setTn _⟩
  · simp only [MethodDesc.toMethod, methOf, hs_isSet] at hs ⊢
    rw [if_neg (by simp [hs]), ← I.map_labs]
    exact ⟨_, isSeqNet_seqTn _⟩

/-- The names with a method. -/
def Rn (c : ℕ) : Prop := ∃ x ∈ I.cnList, c = codeCN x

theorem rn_closed : ∀ c d, I.Rn c → Sum.inr d ∈ I.hs.body c → I.Rn d := by
  rintro c d ⟨x, hx, rfl⟩ hd
  rw [hs_body, List.mem_map] at hd
  obtain ⟨y, hy, he⟩ := hd
  rcases y with a | y
  · simp [itemCode] at he
  · simp only [itemCode, Sum.map_inr, Sum.inr.injEq] at he
    exact ⟨y, I.body_closed hx hy, he.symm⟩

theorem rn_method : ∀ c, I.Rn c → ∃ m ∈ I.desc.toProblem.methods, m.abstractTask = c := by
  rintro c ⟨x, hx, rfl⟩
  exact ⟨_, I.mem_methods.2 ⟨x, hx, rfl⟩, rfl⟩

/-- **Acyclicity.** -/
theorem acyc : FClass.ACYC I.desc.toProblem := by
  refine HTN.Problem.isAcyclic_of_rank _ I.hs.rk fun m hm' t ht c hc => ?_
  obtain ⟨hm, -⟩ := hm'
  obtain ⟨x, -, rfl⟩ := I.mem_methods.1 hm
  apply I.hs.rk_lt
  have key : ∀ ls : List (Bool × ℕ), t ∈ (seqTn ls).toTaskNetwork.T →
      (seqTn ls).toTaskNetwork.α t = Sum.inr c → Sum.inr c ∈ ls.map toLab := by
    intro ls ht hc
    have := mem_of_label_inr ht hc
    exact List.mem_map.2 ⟨_, this, rfl⟩
  simp only [MethodDesc.toMethod, methOf] at ht hc ⊢
  rw [← I.map_labs]
  rcases Bool.eq_false_or_eq_true (isSetCN x) with h | h <;>
    simp only [h, ite_true, ite_false, Bool.false_eq_true] at ht hc
  · exact key _ ht hc
  · exact key _ ht hc

/-! ## The initial task network -/

theorem not_before_single {x a b : ℕ} : ¬ Before [x] a b := by
  rintro ⟨l₁, l₂, h, hb⟩
  rcases l₁ with _ | ⟨y, l₁⟩
  · simp only [List.nil_append, List.cons.injEq] at h
    rw [← h.2] at hb; exact List.not_mem_nil hb
  · have := congrArg List.length h
    simp at this

/-- The two root chains. -/
def rootCs : List (Ch ℕ ℕ ℕ) :=
  [([0], [Sum.inr (codeCN (k := k) .ctl)]), ([1], [Sum.inr (codeCN (k := k) .pool)])]

theorem tnI_toProblem : I.desc.toProblem.tnI = (setTn (tnIL (k := k))).toTaskNetwork := by
  simp only [FProbDesc.toProblem, FProbDesc.tnI, desc]

theorem label_tnIL0 : (setTn (tnIL (k := k))).toTaskNetwork.α 0 = .inr (codeCN (k := k) .ctl) := by
  show (seqTn (tnIL (k := k))).label 0 = _
  rw [label_seqTn (by simp [tnIL])]; rfl

theorem label_tnIL1 : (setTn (tnIL (k := k))).toTaskNetwork.α 1 = .inr (codeCN (k := k) .pool) := by
  show (seqTn (tnIL (k := k))).label 1 = _
  rw [label_seqTn (by simp [tnIL])]; rfl

theorem mem_T_tnIL {t : ℕ} : t ∈ (setTn (tnIL (k := k))).toTaskNetwork.T ↔ t = 0 ∨ t = 1 := by
  simp only [TnDesc.toTaskNetwork, setTn, TnDesc.ids, tnIL, List.mem_toFinset, List.mem_range,
    List.length_cons, List.length_nil]
  omega

/-- **The invariant of the initial task network.** -/
theorem hinv_tnI : HInv I.hs I.desc.toProblem.tnI (I.hs.exI (.inr (codeCN (k := k) .ctl)))
    (I.hs.exMI (.inr (codeCN (k := k) .pool))) := by
  rw [tnI_toProblem]
  refine ⟨rootCs (k := k), by simp [rootCs], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x
    rw [mem_T_tnIL]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [rootCs], by simp [rootCs]⟩
      · exact ⟨1, by simp [rootCs], by simp [rootCs]⟩
    · rintro ⟨j, hj, hx⟩
      simp only [rootCs, List.length_cons, List.length_nil] at hj
      interval_cases j <;> simp [rootCs] at hx <;> simp [hx]
  · intro x y
    refine ⟨fun h => absurd h (setTn_not_ord _ x y), ?_⟩
    rintro ⟨j, hj, h⟩
    simp only [rootCs, List.length_cons, List.length_nil] at hj
    interval_cases j <;> exact absurd h not_before_single
  · intro j hj
    simp only [rootCs, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simp only [rootCs]; exact congrArg (· :: []) label_tnIL0
    · simp only [rootCs]; exact congrArg (· :: []) label_tnIL1
  · intro j hj
    simp only [rootCs, List.length_cons, List.length_nil] at hj
    interval_cases j <;> simp [rootCs]
  · intro i j hi hj hij x hx hx'
    simp only [rootCs, List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;> simp_all [rootCs]
  · intro j hj c hc hS
    simp only [rootCs, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simp only [rootCs, List.getElem_cons_zero, List.mem_singleton, Sum.inr.injEq] at hc
      subst hc; rw [hs_isSet] at hS; simp [isSetCN] at hS
    · simp only [rootCs, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_singleton,
        Sum.inr.injEq] at hc
      subst hc; simp [rootCs]
  · simp [rootCs]
  · simp only [poolE, rootCs, List.tail_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rfl

theorem rn_tnI : ∀ t ∈ I.desc.toProblem.tnI.T, ∀ c, I.desc.toProblem.tnI.α t = .inr c → I.Rn c := by
  rw [tnI_toProblem]
  intro t ht c hc
  rcases mem_T_tnIL.1 ht with rfl | rfl
  · rw [label_tnIL0, Sum.inr.injEq] at hc; exact ⟨_, I.mem_cnList_ctl, hc.symm⟩
  · rw [label_tnIL1, Sum.inr.injEq] at hc; exact ⟨_, I.mem_cnList_pool, hc.symm⟩

/-! ## The transfer to the coded names -/

theorem toProblem_δ (d : FProbDesc) : d.toProblem.δ = d.δ := rfl

theorem toAction_actOf (nm : ℕ) (p : List (Tok Gate (DK k)) × List (List (Tok Gate (DK k)) × List (Tok Gate (DK k)))) :
    (actOf nm p).toAction = encAct codeTok (listAct p.1 [] p.2) :=
  toAction_enc codeTok nm p.1 [] p.2

/-- Pool actions of the instance. -/
def AP (a : PA (SymK k) (OK k)) : Prop := ∀ o, a = .opt o → o ∈ I.opts

theorem paList_of_AP (hsyms : ∀ τ, τ ∈ I.syms) {a : PA (SymK k) (OK k)} (ha : I.AP a) : a ∈ I.paList := by
  rcases a with τ | _ | _ | τ | o
  · simp [paList, hsyms τ]
  · simp [paList]
  · simp [paList]
  · simp [paList, hsyms τ]
  · simp [paList, ha o rfl]

theorem size_map_nP (M : Multiset (List (PA (SymK k) (OK k)))) :
    WSys.size (M.map (List.map nP)) = WSys.size M := by
  simp [WSys.size, Multiset.map_map]

variable (hnone : none ∈ I.syms)
include hnone

theorem δ_ctl {x : CI Gate Pl} (hx : x ≠ .refill) :
    I.desc.toProblem.δ (nC x) = encAct codeTok (I.X0.sys.δC x) := by
  have hm : actOf (nC x) (ctlLists (k := k) I.L x) ∈ I.desc.actions := by
    rw [actions_desc]; exact I.mem_acts.2 (Or.inl ⟨x, mem_ciList x hx, rfl⟩)
  have h := FProbDesc.δ_of_mem (I.valid hnone) hm
  rw [name_actOf] at h
  rw [toProblem_δ, h, toAction_actOf, ctlLists_eq I.L I.S x hx]

theorem δ_pool {a : PA (SymK k) (OK k)} (ha : a ∈ I.paList) :
    I.desc.toProblem.δ (nP a) = encAct codeTok (I.X0.sys.δP a) := by
  have hm : actOf (nP a) (poolLists a) ∈ I.desc.actions := by
    rw [actions_desc]; exact I.mem_acts.2 (Or.inr (Or.inr ⟨a, ha, rfl⟩))
  have h := FProbDesc.δ_of_mem (I.valid hnone) hm
  rw [name_actOf] at h
  rw [toProblem_δ, h, toAction_actOf, poolLists_eq I.L I.S a]

theorem δ_refill : I.desc.toProblem.δ (nC .refill) = I.refillAct.toAction := by
  have hm : I.refillAct ∈ I.desc.actions := by
    rw [actions_desc]; exact I.mem_acts.2 (Or.inr (Or.inl rfl))
  have h := FProbDesc.δ_of_mem (I.valid hnone) hm
  rw [toProblem_δ]; exact h

/-- **The hypotheses of the transfer.** -/
theorem transferHyp (hsyms : ∀ τ, τ ∈ I.syms) :
    TransferHyp codeTok I.X0.sys.δC I.X0.sys.δP I.desc.toProblem.δ I.desc.toProblem.δ nC nP CI.refill
      I.R I.AP where
  inj := codeTok_inj
  injP := nP_inj
  ctl x hx := I.δ_ctl hnone hx
  pool x hx := I.δ_pool hnone (I.paList_of_AP hsyms hx)
  trash₁ M s _ h := WSys.cwin_refill _ I.R M s h
  trash₂ M s hAP h := by
    refine cwin_trash (full := {f | f ∈ encL I.fullL}) (AP := fun b => ∃ a, I.AP a ∧ b = nP a)
      (fun s => ?_) ?_ I.R _ s ?_ (by rwa [size_map_nP])
    · rw [I.δ_refill hnone]
      refine ⟨⟨by simp [refillAct, FActDesc.toAction], by simp [refillAct, FActDesc.toAction]⟩, ?_⟩
      rintro s' ⟨e, he, rfl⟩
      simp only [refillAct, FActDesc.toAction, FActDesc.effs, List.mem_singleton, exists_eq_left,
        Set.mem_setOf_eq] at he
      subst he
      intro f hf
      exact Or.inr hf
    · rintro b ⟨a, ha, rfl⟩ s hs
      rw [I.δ_pool hnone (I.paList_of_AP hsyms ha), ← poolLists_eq I.L I.S a, ← toAction_actOf (nP a)]
      refine ⟨fun f hf => hs ?_, by simp [actOf, FActDesc.toAction]⟩
      simp only [actOf, FActDesc.toAction, encL, Set.mem_setOf_eq, List.mem_map] at hf ⊢
      obtain ⟨t, ht, rfl⟩ := hf
      refine ⟨t, ?_, rfl⟩
      rcases a with τ | _ | _ | τ | o <;>
        simp only [poolLists, List.mem_cons, List.not_mem_nil, or_false] at ht
      · subst ht; simp [fullL, mem_gates]
      · subst ht; simp [fullL, mem_gates]
      · subst ht; simp [fullL, mem_gates]
      · subst ht; simp [fullL, mem_gates]
      · rcases ht with rfl | rfl | rfl | rfl
        · simp [fullL, mem_gates]
        all_goals exact List.mem_append_right _ (List.mem_flatMap.2 ⟨o, ha o rfl, by simp⟩)
    · intro c hc b hb
      obtain ⟨c', hc', rfl⟩ := Multiset.mem_map.1 hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
      exact ⟨a, hAP c' hc' a ha, rfl⟩

end Inst

/-! ## The chain game of the description is the queue game -/

theorem refill_not_mem_expand {P : Type} : ∀ l : List (AcycHard.WI Gate P), (CI.refill : CI Gate P) ∉ WSys.expand l
  | [] => by simp [WSys.expand]
  | .win g :: l => by simp [WSys.expand, refill_not_mem_expand l]
  | .plain p :: l => by simp [WSys.expand, refill_not_mem_expand l]

theorem mem_sum_map {α β : Type} (g : α → Multiset β) {x : β} :
    ∀ l : List α, x ∈ (l.map g).sum → ∃ y ∈ l, x ∈ g y
  | [] => by simp
  | a :: l => by
    intro h
    rw [List.map_cons, List.sum_cons, Multiset.mem_add] at h
    rcases h with h | h
    · exact ⟨a, by simp, h⟩
    · obtain ⟨y, hy, h⟩ := mem_sum_map g l h
      exact ⟨y, by simp [hy], h⟩

theorem count_sum_map {α β : Type} [DecidableEq β] (g : α → Multiset β) (x : β) :
    ∀ l : List α, ∀ a ∈ l, (g a).count x ≤ ((l.map g).sum).count x
  | [] => by simp
  | b :: l => by
    intro a ha
    rw [List.map_cons, List.sum_cons, Multiset.count_add]
    rcases List.mem_cons.1 ha with rfl | ha
    · omega
    · have := count_sum_map g x l a ha; omega

namespace Inst

variable (I : Inst k)

/-- **The good instances**: the parameters fit the Savitch program. -/
structure Good (N : NTM (Fin k) (Option Bool)) (c₀ : Config (Fin k) (Option Bool)) : Prop where
  syms : ∀ τ, τ ∈ I.syms
  opts : ∀ o, o ∈ I.opts ↔ o ∈ Δ N c₀ I.L
  cnt : ∀ b, I.cnt b < 2 ^ I.B
  n : I.n < 2 ^ I.B
  supply : FSpec.steps (prog I.S I.K) ≤ I.n
  steps : I.S ≤ FSpec.steps (prog I.S I.K)
  size : WSys.size (FSpec.liveR (Multiset.replicate I.S (none, I.S)) + I.supply) ≤ I.R

variable {I} {N : NTM (Fin k) (Option Bool)} {c₀ : Config (Fin k) (Option Bool)}

theorem Good.rich (h : I.Good N c₀) :
    I.X0.Rich (fun _ => True) (· ∈ Δ N c₀ I.L) I.supply (FSpec.steps (prog I.S I.K)) where
  cells τ _ := by
    refine h.supply.trans (le_trans ?_ (Multiset.count_le_of_le _ (Multiset.le_add_right _ _)))
    refine le_trans ?_ (count_sum_map (fun τ => I.n • ({I.X0.newCell τ} : Multiset _)) _ _ τ (h.syms τ))
    simp
  opts o ho := by
    refine h.supply.trans (le_trans ?_ (Multiset.count_le_of_le _ (Multiset.le_add_left _ _)))
    refine le_trans ?_ (count_sum_map (fun o => I.n • ({[PA.opt o]} : Multiset _)) _ _ o ((h.opts o).2 ho))
    simp
  shape c hc := by
    rcases Multiset.mem_add.1 hc with hc | hc
    · obtain ⟨τ, -, hc⟩ := mem_sum_map _ _ hc
      exact Or.inr (Or.inl ⟨τ, trivial, Multiset.eq_of_mem_replicate (by simpa [Multiset.nsmul_singleton] using hc)⟩)
    · obtain ⟨o, ho, hc⟩ := mem_sum_map _ _ hc
      exact Or.inr (Or.inr ⟨o, (h.opts o).1 ho,
        Multiset.eq_of_mem_replicate (by simpa [Multiset.nsmul_singleton] using hc)⟩)

theorem Good.ap (h : I.Good N c₀) :
    ∀ c ∈ FSpec.liveR (Multiset.replicate I.S (none, I.S)) + I.supply, ∀ a ∈ c, I.AP a := by
  intro c hc a ha o rfl
  rcases Multiset.mem_add.1 hc with hc | hc
  · simp only [FSpec.liveR, Multiset.map_replicate, Multiset.mem_replicate] at hc
    rw [hc.2, cellR_rep] at ha
    simp [rep] at ha
  rcases Multiset.mem_add.1 hc with hc | hc
  · obtain ⟨τ, -, hc⟩ := mem_sum_map _ _ hc
    rw [Multiset.eq_of_mem_replicate (n := I.n) (b := c) (a := I.X0.newCell τ)
      (by simpa [Multiset.nsmul_singleton] using hc)] at ha
    simp [FSpec.newCell, cellR_rep, rep] at ha
  · obtain ⟨o', ho', hc⟩ := mem_sum_map _ _ hc
    rw [Multiset.eq_of_mem_replicate (n := I.n) (b := c) (a := [PA.opt o'])
      (by simpa [Multiset.nsmul_singleton] using hc)] at ha
    simp only [List.mem_singleton, PA.opt.injEq] at ha
    exact ha ▸ ho'

theorem peffs_ne (p : Pl) : ((I.X0).peffs p).Nonempty := by
  cases p
  · exact ⟨_, rfl⟩
  · exact ⟨_, false, rfl⟩
  · exact ⟨_, false, rfl⟩
  · exact ⟨_, rfl⟩

theorem init_toProblem : I.desc.toProblem.init =
    codeTok '' WSys.idle (G := Gate) ({Fct.st (AS.inp 0)} : Set (DK k)) := by
  ext f
  simp [FProbDesc.toProblem, FProbDesc.init, desc, initL, WSys.idle, eq_comm]

/-- **The chain game of the expansions is the queue game of the program.** -/
theorem Good.cwin_iff [Inhabited (Fin k)] (h : I.Good N c₀) :
    CWin I.desc.toProblem.δ I.desc.toProblem.δ (I.hs.exI (.inr (codeCN (k := k) .ctl)))
      (I.hs.exMI (.inr (codeCN (k := k) .pool))) I.desc.toProblem.init ↔
      G N c₀ I.L I.S (prog I.S I.K) (List.replicate I.S none) {Fct.st (.inp 0)} := by
  have hnone : none ∈ I.syms := h.syms none
  rw [I.exI_ctl h.cnt, I.exMI_pool h.cnt (h.cnt .WT) h.n, init_toProblem,
    cwin_transfer (I.transferHyp hnone h.syms) (refill_not_mem_expand _) h.ap
      (le_trans h.size le_rfl)]
  exact FSpec.cwin_iff_qi (X := I.X0) (aS := fun _ => True) (aO := (· ∈ Δ N c₀ I.L))
    peffs_ne (prog I.S I.K) h.rich h.steps none _ I.R h.size

/-- **Fixed methods, strong OD.** -/
theorem Good.strongOD_iff [Inhabited (Fin k)] (h : I.Good N c₀) :
    I.desc.toProblem.StrongODSolvable ↔
      G N c₀ I.L I.S (prog I.S I.K) (List.replicate I.S none) {Fct.st (.inp 0)} := by
  rw [strongOD_iff_hier I.desc.toProblem I.fit I.Rn I.rn_closed I.rn_method I.hinv_tnI
    I.rn_tnI]
  exact h.cwin_iff

/-- **Method-based policies, strong.** -/
theorem Good.mpStrong_iff [Inhabited (Fin k)] (h : I.Good N c₀) :
    I.desc.toProblem.MPStrongSolvable ↔
      G N c₀ I.L I.S (prog I.S I.K) (List.replicate I.S none) {Fct.st (.inp 0)} := by
  rw [Problem.mpStrongSolvable_iff_mpAndOr (FProbDesc.toProblem_wf (I.valid (h.syms none))),
    mpAndOr_iff_hier I.desc.toProblem I.fit I.Rn I.rn_closed I.rn_method I.hinv_tnI I.rn_tnI]
  exact h.cwin_iff

end Inst

end Sav

end AcycHard

end FOND
