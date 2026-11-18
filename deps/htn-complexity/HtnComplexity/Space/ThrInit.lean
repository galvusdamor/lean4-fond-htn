import HtnComplexity.Space.ThrTblComp
import HtnComplexity.Space.ThrWit
import HtnComplexity.Space.SeqSem1
/-!
# The initial configuration of the thread table, characterised locally

Layer (C), semantic half, of the planner P-REG (`NOTES.md` §64–65).  The facts of the thread
table are numbered by `HTN.Space.Thr.enc`; the facts that can occur in an initial configuration
get the numerals of the gadget machine of P-TR where possible (`cfI v` for a fact of the
instance, `cfG (.lab p x)`, `cfG (.nop p)`, `cfG (.len p)`, `cfG (.wit p a)`, `cfG (.cur p)` for
the sweep counter, `cfG .fin` for `done`), and the three new kinds `edge`, `cl`, `nc` get numerals
`cfN` of the same shape with fresh tags.

`HTN.Space.Thr.ThrInitOk d q S` lists the local conditions the machine checks on a guessed
configuration `S`.  They give:

* `HTN.Space.Thr.initG_eq` — the configuration carries exactly the initial fact set of the thread
  system read off the configuration (slots = identifiers numbered by the witness entries);
* `HTN.Space.Thr.hyp_of_initOk` — the hypotheses of the soundness of the table hold;
* `HTN.Space.Thr.iso_of_initOk` — the initial task network is the canonical network of the
  initial thread configuration.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM PTime

/-! ### Numerals of the new initial facts -/

/-- The new kinds of initial facts. -/
inductive NF where
  | edge (x y : ℕ)
  | cl (x y : ℕ)
  | nc (x y : ℕ)
  deriving DecidableEq

/-- The bits of a new initial fact: a three-bit tag and two unary numbers. -/
def nbits : NF → List Bool
  | .edge x y => [false, true, true] ++ unary x ++ unary y
  | .cl x y => [true, true, true] ++ unary x ++ unary y
  | .nc x y => [true, true, false] ++ unary x ++ unary y

theorem getLast_nbits (e : NF) : (nbits e).getLast? = some true := by
  cases e <;>
  · rw [nbits, unary, unary, ← List.append_assoc, ← List.append_assoc]
    exact List.getLast?_concat

theorem isCanon_nbits (e : NF) : IsCanon (nbits e) := isCanon_of_getLast (Or.inr (getLast_nbits e))

theorem nbits_ne_nil (e : NF) : nbits e ≠ [] := by cases e <;> simp [nbits]

theorem unary2_parse {x y x' y' : ℕ} (h : unary x ++ unary y = unary x' ++ unary y') :
    x = x' ∧ y = y' := by
  obtain ⟨h1, h2⟩ := unary_parse h
  exact ⟨h1, (unary_parse (r := []) (s := []) (by simpa using h2)).1⟩

theorem nbits_injective : Function.Injective nbits := by
  intro e e' h
  cases e <;> cases e' <;> simp only [nbits, List.append_assoc] at h <;>
    first
    | (simp at h; done)
    | (obtain ⟨rfl, rfl⟩ := unary2_parse (List.append_cancel_left h); rfl)

theorem nbits_ne_gbits (e : NF) (g : GF) : nbits e ≠ gbits g := by
  cases e <;> cases g <;> simp only [nbits, gbits, List.append_assoc] <;>
    first
    | (simp; done)
    | (intro h
       have := congrArg List.length h
       simp [unary] at this
       omega)

/-- The numeral of a new initial fact. -/
def cfN (e : NF) : ℕ := 4 * (2 * natOfBits (nbits e)) + 2

theorem bitsOfNat_cfN (e : NF) : bitsOfNat (cfN e) = gT ++ nbits e := by
  rw [cfN, bitsOfNat_four_add_two,
    bitsOfNat_two_mul (natOfBits_ne_zero_of_isCanon (isCanon_nbits e) (nbits_ne_nil e)),
    isCanon_nbits e]
  rfl

theorem cfN_injective : Function.Injective cfN := by
  intro e e' h
  have := congrArg bitsOfNat h
  rw [bitsOfNat_cfN, bitsOfNat_cfN] at this
  exact nbits_injective (List.append_cancel_left this)

theorem cfN_ne_cfG (e : NF) (g : GF) : cfN e ≠ cfG g := by
  intro h
  have := congrArg bitsOfNat h
  rw [bitsOfNat_cfN, bitsOfNat_cfG] at this
  exact nbits_ne_gbits e g (List.append_cancel_left this)

theorem cfN_ne_cfI (e : NF) (v : ℕ) : cfN e ≠ cfI v := by
  intro h
  have := congrArg bitsOfNat h
  rw [bitsOfNat_cfN, bitsOfNat_cfI] at this
  simp [gT, tagI3] at this

/-! ### The numbering of all facts -/

/-- The numerals of the facts that never occur in an initial configuration. -/
def encR (tag n : ℕ) : ℕ := 4 * Nat.pair tag n + 1

theorem encR_injective {t n t' n' : ℕ} (h : encR t n = encR t' n') : t = t' ∧ n = n' := by
  have : Nat.pair t n = Nat.pair t' n' := by simp only [encR] at h; omega
  have := congrArg Nat.unpair this
  simpa using this

theorem encR_mod (t n : ℕ) : encR t n % 4 = 1 := by simp only [encR]; omega

theorem cfI_mod (v : ℕ) : cfI v % 4 = 2 := by simp only [cfI]; omega

theorem cfG_mod (g : GF) : cfG g % 4 = 2 := by simp only [cfG]; omega

theorem cfN_mod (e : NF) : cfN e % 4 = 2 := by simp only [cfN]; omega

/-- **The numbering of the facts of the thread table.** -/
def enc : TF → ℕ
  | .inst v => cfI v
  | .lab j x => cfG (.lab j x)
  | .nop j => cfG (.nop j)
  | .len p => cfG (.len p)
  | .wit p a => cfG (.wit p a)
  | .edge x y => cfN (.edge x y)
  | .cl x y => cfN (.cl x y)
  | .nc x y => cfN (.nc x y)
  | .swp p => cfG (.cur p)
  | .done => cfG .fin
  | .cur j c => encR 0 (Nat.pair j c)
  | .blk j μ => encR 1 (Nat.pair j μ)
  | .tok j μ x => encR 2 (Nat.pair j (Nat.pair μ x))
  | .don j μ x => encR 3 (Nat.pair j (Nat.pair μ x))
  | .fin j => encR 4 j
  | .ok i j => encR 5 (Nat.pair i j)
  | .rch x y => encR 6 (Nat.pair x y)
  | .unused p => encR 7 p

/-- The facts, sorted by the kind of their numerals. -/
def classify : TF → (ℕ ⊕ GF) ⊕ (NF ⊕ (ℕ × ℕ))
  | .inst v => .inl (.inl v)
  | .lab j x => .inl (.inr (.lab j x))
  | .nop j => .inl (.inr (.nop j))
  | .len p => .inl (.inr (.len p))
  | .wit p a => .inl (.inr (.wit p a))
  | .swp p => .inl (.inr (.cur p))
  | .done => .inl (.inr .fin)
  | .edge x y => .inr (.inl (.edge x y))
  | .cl x y => .inr (.inl (.cl x y))
  | .nc x y => .inr (.inl (.nc x y))
  | .cur j c => .inr (.inr (0, Nat.pair j c))
  | .blk j μ => .inr (.inr (1, Nat.pair j μ))
  | .tok j μ x => .inr (.inr (2, Nat.pair j (Nat.pair μ x)))
  | .don j μ x => .inr (.inr (3, Nat.pair j (Nat.pair μ x)))
  | .fin j => .inr (.inr (4, j))
  | .ok i j => .inr (.inr (5, Nat.pair i j))
  | .rch x y => .inr (.inr (6, Nat.pair x y))
  | .unused p => .inr (.inr (7, p))

theorem classify_injective : Function.Injective classify := by
  intro f f' h
  cases f <;> cases f' <;> simp_all [classify, Nat.pair_eq_pair]

/-- The numeral of a sorted fact. -/
def encC : (ℕ ⊕ GF) ⊕ (NF ⊕ (ℕ × ℕ)) → ℕ
  | .inl (.inl v) => cfI v
  | .inl (.inr g) => cfG g
  | .inr (.inl e) => cfN e
  | .inr (.inr (t, n)) => encR t n

theorem encC_injective : Function.Injective encC := by
  intro a b h
  rcases a with (v | g) | (e | ⟨t, n⟩) <;> rcases b with (v' | g') | (e' | ⟨t', n'⟩) <;>
    simp only [encC] at h
  · rw [cfI_injective h]
  · exact absurd h (cfI_ne_cfG _ _)
  · exact absurd h.symm (cfN_ne_cfI _ _)
  · have := cfI_mod v; have := encR_mod t' n'; omega
  · exact absurd h.symm (cfI_ne_cfG _ _)
  · rw [cfG_injective h]
  · exact absurd h.symm (cfN_ne_cfG _ _)
  · have := cfG_mod g; have := encR_mod t' n'; omega
  · exact absurd h (cfN_ne_cfI _ _)
  · exact absurd h (cfN_ne_cfG _ _)
  · rw [cfN_injective h]
  · have := cfN_mod e; have := encR_mod t' n'; omega
  · have := cfI_mod v'; have := encR_mod t n; omega
  · have := cfG_mod g'; have := encR_mod t n; omega
  · have := cfN_mod e'; have := encR_mod t n; omega
  · obtain ⟨rfl, rfl⟩ := encR_injective h; rfl

theorem enc_eq (f : TF) : enc f = encC (classify f) := by cases f <;> rfl

theorem enc_injective : Function.Injective enc := by
  intro f f' h
  rw [enc_eq, enc_eq] at h
  exact classify_injective (encC_injective h)

/-! ### The local conditions -/

/-- The number of identifiers of the initial task network. -/
noncomputable def nIds (q : InstDesc) : ℕ := q.tnI.ids.toFinset.card

/-- **The conditions the initial test checks** on a configuration `S` (a list of numerals), for
the domain description `d` (through its vocabulary) and the instance `q`. -/
structure ThrInitOk (d : DomDesc) (q : InstDesc) (S : List ℕ) : Prop where
  shape : ∀ f ∈ S, (∃ v, f = cfI v) ∨ (∃ g, f = cfG g) ∨ (∃ e, f = cfN e)
  inst : ∀ v, cfI v ∈ S ↔ v ∈ q.initList
  cur : ∀ p, cfG (.cur p) ∈ S ↔ p = 0
  fin : cfG .fin ∉ S
  wit : WitR q.tnI (witList S)
  lab : ∀ p x, cfG (.lab p x) ∈ S ↔ ∃ i ∈ q.tnI.ids, cfG (.wit p i) ∈ S ∧ q.tnI.label i = x
  nop : ∀ p, cfG (.nop p) ∈ S ↔
    ∃ i ∈ q.tnI.ids, cfG (.wit p i) ∈ S ∧ unknownPrimB d (q.tnI.label i) = true
  len : ∀ k, cfG (.len k) ∈ S ↔
    (∀ i ∈ q.tnI.ids, cfG (.wit k i) ∉ S) ∧ (k = 0 ∨ ∃ i ∈ q.tnI.ids, cfG (.wit (k - 1) i) ∈ S)
  edge : ∀ x y, cfN (.edge x y) ∈ S ↔
    ∃ e ∈ q.tnI.ordList, cfG (.wit x e.1) ∈ S ∧ cfG (.wit y e.2) ∈ S
  cl1 : ∀ x y, cfN (.edge x y) ∈ S → cfN (.cl x y) ∈ S
  cl2 : ∀ x y z, cfN (.cl x y) ∈ S → cfN (.edge y z) ∈ S → cfN (.cl x z) ∈ S
  nc : ∀ x y, cfN (.nc x y) ∈ S → cfN (.cl x y) ∉ S
  clpos : ∀ x y, cfN (.cl x y) ∈ S → (∃ a, cfG (.wit x a) ∈ S) ∧ (∃ b, cfG (.wit y b) ∈ S)
  ncpos : ∀ x y, cfN (.nc x y) ∈ S → (∃ a, cfG (.wit x a) ∈ S) ∧ (∃ b, cfG (.wit y b) ∈ S)

/-- The identifier in the slot `j`. -/
noncomputable def slotId (q : InstDesc) (S : List ℕ) (j : ℕ) : ℕ := wnode q.tnI (witList S) j

/-- **The thread system read off a configuration.** -/
noncomputable def parOf (d : DomDesc) (q : InstDesc) (S : List ℕ) : Par where
  d := d
  k := nIds q
  lab j := q.tnI.label (slotId q S j)
  O i j := i < nIds q ∧ j < nIds q ∧ q.tnI.ordOf (slotId q S i) (slotId q S j)

/-- **The graph data read off a configuration.** -/
def grOf (S : List ℕ) : Gr where
  E x y := cfN (.edge x y) ∈ S
  Cl x y := cfN (.cl x y) ∈ S
  NC x y := cfN (.nc x y) ∈ S
  W p a := cfG (.wit p a) ∈ S

section Sound

variable {d : DomDesc} {q : InstDesc} {S : List ℕ}

theorem ThrInitOk.slot_spec (h : ThrInitOk d q S) {j : ℕ} (hj : j < nIds q) :
    slotId q S j ∈ q.tnI.ids ∧ cfG (.wit j (slotId q S j)) ∈ S := by
  obtain ⟨h1, h2⟩ := h.wit.wnode_spec hj
  refine ⟨h1, mem_witList.1 ?_⟩
  have := mem_wpos (h.wit.total _ h1)
  rwa [h2] at this

/-- A witness entry of an identifier sits in its slot. -/
theorem ThrInitOk.slot_of_wit (h : ThrInitOk d q S) {j i : ℕ} (hi : i ∈ q.tnI.ids)
    (hw : cfG (.wit j i) ∈ S) : j < nIds q ∧ slotId q S j = i := by
  have hw' := mem_witList.2 hw
  have hj : j = wpos (witList S) i := (h.wit.mem_iff hi).1 hw'
  subst hj
  exact ⟨h.wit.wpos_lt hi, h.wit.wnode_wpos hi⟩

theorem ThrInitOk.len_iff (h : ThrInitOk d q S) (k : ℕ) : cfG (.len k) ∈ S ↔ k = nIds q := by
  rw [h.len]
  have h1 : (∀ i ∈ q.tnI.ids, cfG (.wit k i) ∉ S) ↔ ¬ k < nIds q := by
    rw [nIds, ← h.wit.exists_id_iff]
    simp [mem_witList]
  have h2 : (∃ i ∈ q.tnI.ids, cfG (.wit (k - 1) i) ∈ S) ↔ k - 1 < nIds q := by
    rw [nIds, ← h.wit.exists_id_iff]
    simp [mem_witList]
  rw [h1, h2]
  omega

theorem mem_S_ne_encR (h : ThrInitOk d q S) (t n : ℕ) : encR t n ∉ S := by
  intro hm
  have h4 := encR_mod t n
  rcases h.shape _ hm with ⟨v, hv⟩ | ⟨g, hg⟩ | ⟨e, he⟩
  · have := cfI_mod v; omega
  · have := cfG_mod g; omega
  · have := cfN_mod e; omega

/-- **The configuration carries exactly the initial fact set of the thread system.** -/
theorem initG_eq (h : ThrInitOk d q S) :
    enc ⁻¹' {n | n ∈ S} = initG (parOf d q S) (grOf S) {v | v ∈ q.initList} := by
  ext f
  simp only [Set.mem_preimage, Set.mem_setOf_eq, initG, initF]
  cases f with
  | inst v => exact h.inst v
  | lab j x =>
    show cfG (.lab j x) ∈ S ↔ j < nIds q ∧ x = q.tnI.label (slotId q S j)
    rw [h.lab]
    constructor
    · rintro ⟨i, hi, hw, rfl⟩
      obtain ⟨hj, hs⟩ := h.slot_of_wit hi hw
      exact ⟨hj, by rw [hs]⟩
    · rintro ⟨hj, rfl⟩
      exact ⟨_, (h.slot_spec hj).1, (h.slot_spec hj).2, rfl⟩
  | nop j =>
    show cfG (.nop j) ∈ S ↔ j < nIds q ∧ Unk d (q.tnI.label (slotId q S j))
    rw [h.nop]
    constructor
    · rintro ⟨i, hi, hw, hu⟩
      obtain ⟨hj, hs⟩ := h.slot_of_wit hi hw
      exact ⟨hj, by rw [hs]; exact hu⟩
    · rintro ⟨hj, hu⟩
      exact ⟨_, (h.slot_spec hj).1, (h.slot_spec hj).2, hu⟩
  | len p => exact h.len_iff p
  | wit p a => exact Iff.rfl
  | edge x y => exact Iff.rfl
  | cl x y => exact Iff.rfl
  | nc x y => exact Iff.rfl
  | swp p => exact h.cur p
  | done => exact iff_of_false h.fin id
  | cur j c => exact iff_of_false (mem_S_ne_encR h _ _) id
  | blk j μ => exact iff_of_false (mem_S_ne_encR h _ _) id
  | tok j μ x => exact iff_of_false (mem_S_ne_encR h _ _) id
  | don j μ x => exact iff_of_false (mem_S_ne_encR h _ _) id
  | fin j => exact iff_of_false (mem_S_ne_encR h _ _) id
  | ok i j => exact iff_of_false (mem_S_ne_encR h _ _) id
  | rch x y => exact iff_of_false (mem_S_ne_encR h _ _) id
  | unused p => exact iff_of_false (mem_S_ne_encR h _ _) id

/-- Reachability in the graph of the configuration is the order of the nodes. -/
theorem transGen_iff (h : ThrInitOk d q S) {x y : ℕ} :
    Relation.TransGen (grOf S).E x y ↔
      ∃ a b, cfG (.wit x a) ∈ S ∧ cfG (.wit y b) ∈ S ∧ q.tnI.preOrd a b := by
  constructor
  · intro hxy
    induction hxy with
    | single he =>
      obtain ⟨e, he, h1, h2⟩ := (h.edge _ _).1 he
      exact ⟨_, _, h1, h2, .single he⟩
    | tail _ he ih =>
      obtain ⟨a, b, h1, h2, hab⟩ := ih
      obtain ⟨e, he, h3, h4⟩ := (h.edge _ _).1 he
      have := h.wit.inj _ _ _ (mem_witList.2 h2) (mem_witList.2 h3)
      subst this
      exact ⟨a, e.2, h1, h4, hab.tail he⟩
  · rintro ⟨a, b, h1, h2, hab⟩
    induction hab generalizing y with
    | single hab =>
      exact .single ((h.edge _ _).2 ⟨_, hab, h1, h2⟩)
    | @tail b c _ hbc ih =>
      obtain ⟨z, hz⟩ := (h.wit.endp _ hbc).1
      exact (ih (mem_witList.1 hz)).tail ((h.edge _ _).2 ⟨_, hbc, mem_witList.1 hz, h2⟩)

theorem transGen_slot_iff (h : ThrInitOk d q S) {i j : ℕ} (hi : i < nIds q) (hj : j < nIds q) :
    Relation.TransGen (grOf S).E i j ↔ q.tnI.preOrd (slotId q S i) (slotId q S j) := by
  rw [transGen_iff h]
  constructor
  · rintro ⟨a, b, h1, h2, hab⟩
    have e1 := h.wit.inj _ _ _ (mem_witList.2 h1) (mem_witList.2 (h.slot_spec hi).2)
    have e2 := h.wit.inj _ _ _ (mem_witList.2 h2) (mem_witList.2 (h.slot_spec hj).2)
    rwa [← e1, ← e2]
  · intro hab
    exact ⟨_, _, (h.slot_spec hi).2, (h.slot_spec hj).2, hab⟩

/-- **The hypotheses of the soundness of the table hold.** -/
theorem hyp_of_initOk (hreg : d.MethodsReg) (h : ThrInitOk d q S) {N : ℕ} (hN : nIds q ≤ N) :
    Hyp (parOf d q S) (grOf S) N where
  good :=
    { reg := hreg
      irrefl := fun i hO => hO.2.2.2.2.2 hO.2.2.2.2.1
      trans := fun h1 h2 => ⟨h1.1, h2.2.1,
        (TnDesc.toTaskNetwork_wf q.tnI).trans h1.2.2 h2.2.2⟩ }
  kN := hN
  hO i hi j hj := by
    have hi' : i < nIds q := hi
    have hj' : j < nIds q := hj
    show (i < nIds q ∧ j < nIds q ∧ q.tnI.ordOf _ _) ↔ _
    rw [transGen_slot_iff h hi' hj', transGen_slot_iff h hj' hi']
    simp only [TnDesc.ordOf, hi', hj', (h.slot_spec hi').1, (h.slot_spec hj').1, true_and]
  cl1 x y := h.cl1 x y
  cl2 x y z := h.cl2 x y z
  nc x y := h.nc x y

/-- **The initial task network is the canonical network of the initial thread
configuration.** -/
theorem iso_of_initOk (h : ThrInitOk d q S) :
    q.tnI.toTaskNetwork.Iso (toTN (parOf d q S) (fun _ => .pend)) := by
  set ws := witList S
  have hk : ∀ i ∈ q.tnI.ids, wpos ws i < nIds q := fun i hi => h.wit.wpos_lt hi
  have hmem : ∀ j, j < nIds q → tid j 0 ∈ tasks (parOf d q S) (fun _ => .pend) := fun j hj =>
    mem_tasks_of (P := parOf d q S) hj (by simp [thTasks])
  have htask : ∀ t ∈ tasks (parOf d q S) (fun _ => TSt.pend), ∃ j < nIds q, t = tid j 0 := by
    intro t ht
    obtain ⟨hj, ht⟩ := mem_tasks.1 ht
    simp only [thTasks, Finset.mem_singleton] at ht
    exact ⟨_, hj, ht⟩
  refine ⟨fun a => tid (wpos ws a) 0, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    exact hmem _ (hk a (List.mem_toFinset.1 ha))
  · intro a ha b hb heq
    have := (tid_inj.1 heq).1
    exact h.wit.wpos_inj (h.wit.total a (List.mem_toFinset.1 ha))
      (h.wit.total b (List.mem_toFinset.1 hb)) this
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := htask t ht
    refine ⟨slotId q S j, List.mem_toFinset.2 (h.slot_spec hj).1, ?_⟩
    have := (h.wit.wnode_spec hj).2
    simp only [slotId] at this ⊢
    rw [this]
  · intro a ha b hb
    have ha' := List.mem_toFinset.1 ha
    have hb' := List.mem_toFinset.1 hb
    rw [toTN_ord]
    simp only [rel, unpair_tid, reduceCtorEq, false_and, exists_false, and_false,
      false_or, lt_irrefl]
    have hsa : slotId q S (wpos ws a) = a := h.wit.wnode_wpos ha'
    have hsb : slotId q S (wpos ws b) = b := h.wit.wnode_wpos hb'
    constructor
    · intro hab
      refine ⟨hmem _ (hk a ha'), hmem _ (hk b hb'), fun he => ?_,
        ⟨hk a ha', hk b hb', by rw [hsa, hsb]; exact hab⟩⟩
      have := h.wit.wpos_inj (h.wit.total a ha') (h.wit.total b hb') he
      subst this
      exact hab.2.2.2 hab.2.2.1
    · rintro ⟨-, -, -, -, -, hab⟩
      rwa [hsa, hsb] at hab
  · intro a ha
    have ha' := List.mem_toFinset.1 ha
    rw [toTN_α]
    simp only [unpair_tid, thLabel, parOf, TnDesc.toTaskNetwork_α]
    rw [show slotId q S (wpos ws a) = a from h.wit.wnode_wpos ha']

end Sound

end Thr

end Space

end HTN
