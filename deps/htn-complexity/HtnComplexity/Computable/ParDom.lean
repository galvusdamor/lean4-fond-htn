import HtnComplexity.Computable.ParSource
import HtnPlanning.Computable.Bodies
import HtnComplexity.Computable.ChainTn
/-!
# The parallel product domain: a regular domain that carries a whole configuration in its names

`HtnComplexity/Computable/ProdDom.lean` roots a bounded initial **chain** inside the regular
classes by folding the rest of the chain into the compound names.  An initial task network of
several *unordered* tasks cannot be folded that way: the refinements of the tasks interleave, so
the compiled domain has to keep track of *all* the tasks at once, and of how far each of them has
got.  For a **totally ordered** regular source domain that is a bounded amount of information:
what is left of a task is a suffix of the body of the method last applied to it, and there are
at most `|d| + |heads| + 1` such suffixes.

The compiled names are therefore whole **configurations**

    L = [xs₁, …, xs_j]   (`HTN.Syn.ParCfg`)

— one remaining task sequence per initial task — and the methods of the compiled domain perform
one step of one process:

* `xs_i = a :: xs` with `a` an action: execute `a` and continue with `L[i := xs]`
  (the body `HTN.Syn.parStepTn`, a chain of two tasks);
* `xs_i = c :: xs` with `c` a compound name: replace `c` by the body of one of its methods and
  continue with `L[i := body ++ xs]` (the body `HTN.Syn.singleTn`, a single compound task);
* every process finished: the empty body.

Every body has at most one compound task and it comes last, so the compiled domain is regular
*and* totally ordered.  This file contains the construction and its syntactic properties; its
correctness is `HtnComplexity/Computable/ParCorrect.lean`.
-/

namespace HTN

namespace Syn

/-! ### Configurations -/

/-- The remaining task sequence of one process. -/
abbrev ParEntry : Type := List (ℕ ⊕ ℕ)

/-- A **configuration**: one remaining task sequence per initial task. -/
abbrev ParCfg : Type := List ParEntry

/-- **The compound name of a configuration.** -/
def parName (L : ParCfg) : ℕ := Encodable.encode L

theorem parName_injective : Function.Injective parName :=
  fun _ _ h => Encodable.encode_injective h

@[simp] theorem parName_inj {L L' : ParCfg} : parName L = parName L' ↔ L = L' :=
  ⟨fun h => parName_injective h, fun h => by rw [h]⟩

/-! ### The two shapes of body -/

/-- The body of a step that executes the action `a` and continues with the configuration
named `c`: the chain of the two tasks. -/
def parStepTn (a c : ℕ) : TnDesc := ([0, 1], [(0, 1)], [(0, false, a), (1, true, c)])

@[simp] theorem seqBody_parStepTn (a c : ℕ) :
    TnDesc.seqBody (parStepTn a c) = [Sum.inl a, Sum.inr c] := rfl

@[simp] theorem seqBody_singleTn (c : ℕ) : TnDesc.seqBody (singleTn c) = [Sum.inr c] := rfl

@[simp] theorem seqBody_nil : TnDesc.seqBody TnDesc.nil = [] := rfl

theorem parStepTn_ord (a c : ℕ) : (parStepTn a c).toTaskNetwork.ord 0 1 :=
  TnDesc.ordB_iff.1 (by rfl)

theorem parStepTn_mem {a c : ℕ} {x : ℕ} (hx : x ∈ (parStepTn a c).toTaskNetwork.T) :
    x = 0 ∨ x = 1 := by
  simp only [TnDesc.toTaskNetwork_T, List.mem_toFinset] at hx
  simpa [parStepTn, TnDesc.ids] using hx

theorem parStepTn_notAbstract (a c : ℕ) : ¬ (parStepTn a c).toTaskNetwork.IsAbstractId 0 := by
  rintro ⟨c', hc'⟩
  exact absurd hc' (by simp [TnDesc.toTaskNetwork, parStepTn, TnDesc.label, TnDesc.lbl])

theorem parStepTn_isTO (a c : ℕ) : (parStepTn a c).toTaskNetwork.IsTotallyOrdered := by
  intro x hx y hy hne
  rcases parStepTn_mem hx with rfl | rfl <;> rcases parStepTn_mem hy with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl (parStepTn_ord a c)
  · exact Or.inr (parStepTn_ord a c)
  · exact absurd rfl hne

theorem parStepTn_isRegular (a c : ℕ) : (parStepTn a c).toTaskNetwork.IsRegular := by
  constructor
  · intro x hx y hy hax hay
    rcases parStepTn_mem hx with rfl | rfl <;> rcases parStepTn_mem hy with rfl | rfl
    · rfl
    · exact absurd hax (parStepTn_notAbstract a c)
    · exact absurd hay (parStepTn_notAbstract a c)
    · rfl
  · intro x hx hax y hy hne
    rcases parStepTn_mem hx with rfl | rfl
    · exact absurd hax (parStepTn_notAbstract a c)
    · rcases parStepTn_mem hy with rfl | rfl
      · exact parStepTn_ord a c
      · exact absurd rfl hne

/-! ### The pool of entries and of configurations -/

/-- The suffixes of a list, as a `foldr` — the shape that makes it primitive recursive. -/
def suffixesOf {α : Type} (l : List α) : List (List α) :=
  l.foldr (fun a r => (a :: r.headI) :: r) [[]]

@[simp] theorem suffixesOf_nil {α : Type} : suffixesOf ([] : List α) = [[]] := rfl

theorem suffixesOf_headI {α : Type} (l : List α) : (suffixesOf l).headI = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      show a :: (suffixesOf l).headI = a :: l
      rw [ih]

theorem suffixesOf_cons {α : Type} (a : α) (l : List α) :
    suffixesOf (a :: l) = (a :: l) :: suffixesOf l := by
  simp only [suffixesOf, List.foldr_cons]
  rw [show (List.foldr (fun a r => (a :: r.headI) :: r) [[]] l).headI = l from
    suffixesOf_headI l]

theorem mem_suffixesOf_self {α : Type} (l : List α) : l ∈ suffixesOf l := by
  cases l with
  | nil => simp
  | cons a l => rw [suffixesOf_cons]; exact List.mem_cons_self

theorem nil_mem_suffixesOf {α : Type} (l : List α) : [] ∈ suffixesOf l := by
  induction l with
  | nil => simp
  | cons a l ih => rw [suffixesOf_cons]; exact List.mem_cons_of_mem _ ih

theorem tail_mem_suffixesOf {α : Type} {l s : List α} {a : α} (h : a :: s ∈ suffixesOf l) :
    s ∈ suffixesOf l := by
  induction l with
  | nil => rw [suffixesOf_nil] at h; simp at h
  | cons b l ih =>
      rw [suffixesOf_cons] at h ⊢
      rcases List.mem_cons.1 h with heq | hmem
      · rw [show s = l from (List.cons.inj heq).2]
        exact List.mem_cons_of_mem _ (mem_suffixesOf_self l)
      · exact List.mem_cons_of_mem _ (ih hmem)

/-- The lists of length exactly `n` over a list of entries. -/
def parTuplesEq : ℕ → List ParEntry → List ParCfg
  | 0, _ => [[]]
  | n + 1, l => l.flatMap fun c => (parTuplesEq n l).map (c :: ·)

/-- The lists of length at most `k` over a list of entries. -/
def parTuplesLe (k : ℕ) (l : List ParEntry) : List ParCfg :=
  (List.range (k + 1)).flatMap fun n => parTuplesEq n l

theorem mem_parTuplesEq {n : ℕ} {l : List ParEntry} {L : ParCfg} :
    L ∈ parTuplesEq n l ↔ L.length = n ∧ ∀ x ∈ L, x ∈ l := by
  induction n generalizing L with
  | zero =>
      simp only [parTuplesEq, List.mem_singleton, List.length_eq_zero_iff]
      constructor
      · rintro rfl; exact ⟨rfl, by simp⟩
      · rintro ⟨h, -⟩; exact h
  | succ n ih =>
      simp only [parTuplesEq, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨c, hc, us, hus, rfl⟩
        obtain ⟨hlen, hmem⟩ := ih.1 hus
        refine ⟨by simp [hlen], ?_⟩
        rintro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hc
        · exact hmem x hx
      · rintro ⟨hlen, hmem⟩
        rcases L with _ | ⟨c, us⟩
        · simp at hlen
        · exact ⟨c, hmem c (by simp), us, ih.2 ⟨by simpa using hlen,
            fun x hx => hmem x (List.mem_cons_of_mem _ hx)⟩, rfl⟩

theorem mem_parTuplesLe {k : ℕ} {l : List ParEntry} {L : ParCfg} :
    L ∈ parTuplesLe k l ↔ L.length ≤ k ∧ ∀ x ∈ L, x ∈ l := by
  simp only [parTuplesLe, List.mem_flatMap, List.mem_range, mem_parTuplesEq]
  constructor
  · rintro ⟨n, hn, hlen, hmem⟩
    exact ⟨by omega, hmem⟩
  · rintro ⟨hlen, hmem⟩
    exact ⟨L.length, by omega, rfl, hmem⟩

theorem length_parTuplesEq (n : ℕ) (l : List ParEntry) :
    (parTuplesEq n l).length = l.length ^ n := by
  induction n with
  | zero => simp [parTuplesEq]
  | succ n ih =>
      rw [parTuplesEq, List.length_flatMap]
      simp only [List.length_map, ih, List.map_const', List.sum_replicate, smul_eq_mul]
      rw [pow_succ, Nat.mul_comm]

theorem length_parTuplesLe (k : ℕ) (l : List ParEntry) :
    (parTuplesLe k l).length ≤ (k + 1) * (l.length + 1) ^ k := by
  have hle : ∀ n ≤ k, (parTuplesEq n l).length ≤ (l.length + 1) ^ k := by
    intro n hn
    rw [length_parTuplesEq]
    calc l.length ^ n ≤ (l.length + 1) ^ n := Nat.pow_le_pow_left (by omega) n
      _ ≤ (l.length + 1) ^ k := Nat.pow_le_pow_right (by omega) hn
  have h := length_flatMap_le (List.range (k + 1)) (fun n => parTuplesEq n l)
    ((l.length + 1) ^ k) (fun n hn => hle n (by simpa [Nat.lt_succ_iff] using hn))
  simpa [parTuplesLe] using h

/-- **The entries a configuration of the compiled domain may contain**: an initial compound
task, or a suffix of the body of a listed method. -/
def parEntries (d : DomDesc) : List ParEntry :=
  [] :: (d.heads.map fun c => [Sum.inr c]) ++
    d.methods.flatMap fun e => suffixesOf (TnDesc.seqBody e.2)

/-- **The configurations of the compiled domain**: at most `k` entries. -/
def parCfgs (k : ℕ) (d : DomDesc) : List ParCfg := parTuplesLe k (parEntries d)

theorem mem_parEntries_nil (d : DomDesc) : ([] : ParEntry) ∈ parEntries d := by
  simp [parEntries]

theorem mem_parEntries_head {d : DomDesc} {c : ℕ} (hc : c ∈ d.heads) :
    ([Sum.inr c] : ParEntry) ∈ parEntries d := by
  simp only [parEntries, List.cons_append, List.mem_cons, List.mem_append, List.mem_map]
  exact Or.inr (Or.inl ⟨c, hc, rfl⟩)

theorem mem_parEntries_body {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods)
    {s : ParEntry} (hs : s ∈ suffixesOf (TnDesc.seqBody e.2)) : s ∈ parEntries d := by
  simp only [parEntries, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap]
  exact Or.inr (Or.inr ⟨e, he, hs⟩)

/-! ### The methods of the compiled domain -/

/-- The methods that step the `i`-th process of the configuration `L`. -/
def parStepMethods (d : DomDesc) (L : ParCfg) (i : ℕ) : List MethodDesc :=
  match L.getI i with
  | [] => []
  | Sum.inl a :: xs => [(parName L, parStepTn a (parName (L.set i xs)))]
  | Sum.inr c :: xs =>
      (d.methods.filter fun e => e.1 = c).map fun e =>
        (parName L, singleTn (parName (L.set i (TnDesc.seqBody e.2 ++ xs))))

/-- The methods of the compiled domain for the configuration `L`. -/
def parMethodsOf (d : DomDesc) (L : ParCfg) : List MethodDesc :=
  (if L.all (fun xs => xs.isEmpty) then [(parName L, TnDesc.nil)] else []) ++
    (List.range L.length).flatMap (parStepMethods d L)

/-- **The methods of the compiled domain.** -/
def parMethods (k : ℕ) (d : DomDesc) : List MethodDesc :=
  (parCfgs k d).flatMap (parMethodsOf d)

/-- **The compiled domain**: the actions of the source, and one method per step of one process
of a configuration. -/
def parDom (k : ℕ) (d : DomDesc) : DomDesc := (d.actions, parMethods k d)

/-- **The compiled instance**: the configuration of the initial task network, as a single
compound task. -/
def parInst (q : InstDesc) : InstDesc :=
  (q.initList, q.goalList,
    singleTn (parName (q.tnI.compoundNames.map fun c => [Sum.inr c])))

@[simp] theorem parDom_actions (k : ℕ) (d : DomDesc) : (parDom k d).actions = d.actions := rfl

@[simp] theorem parDom_methods (k : ℕ) (d : DomDesc) : (parDom k d).methods = parMethods k d :=
  rfl

@[simp] theorem parInst_initList (q : InstDesc) : (parInst q).initList = q.initList := rfl

@[simp] theorem parInst_goalList (q : InstDesc) : (parInst q).goalList = q.goalList := rfl

@[simp] theorem parInst_tnI (q : InstDesc) :
    (parInst q).tnI =
      singleTn (parName (q.tnI.compoundNames.map fun c => [Sum.inr c])) := rfl

/-! ### Which methods the compiled domain has -/

theorem mem_parMethods_iff {k : ℕ} {d : DomDesc} {m : MethodDesc} :
    m ∈ parMethods k d ↔ ∃ L ∈ parCfgs k d, m ∈ parMethodsOf d L := by
  simp [parMethods]

theorem mem_parMethodsOf_done {d : DomDesc} {L : ParCfg} (h : ∀ xs ∈ L, xs = []) :
    ((parName L, TnDesc.nil) : MethodDesc) ∈ parMethodsOf d L := by
  have hall : L.all (fun xs => xs.isEmpty) = true := by
    simp only [List.all_eq_true, List.isEmpty_iff]
    exact fun xs hxs => h xs hxs
  simp [parMethodsOf, hall]

theorem mem_parMethodsOf_prim {d : DomDesc} {L : ParCfg} {i : ℕ} (hi : i < L.length)
    {a : ℕ} {xs : ParEntry} (hL : L.getI i = Sum.inl a :: xs) :
    ((parName L, parStepTn a (parName (L.set i xs))) : MethodDesc) ∈ parMethodsOf d L := by
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨i, by simpa using hi, ?_⟩)
  rw [parStepMethods, hL]
  simp

theorem mem_parMethodsOf_comp {d : DomDesc} {L : ParCfg} {i : ℕ} (hi : i < L.length)
    {c : ℕ} {xs : ParEntry} (hL : L.getI i = Sum.inr c :: xs)
    {e : MethodDesc} (he : e ∈ d.methods) (hc : e.1 = c) :
    ((parName L, singleTn (parName (L.set i (TnDesc.seqBody e.2 ++ xs)))) : MethodDesc) ∈
      parMethodsOf d L := by
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨i, by simpa using hi, ?_⟩)
  rw [parStepMethods, hL]
  exact List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simpa using hc⟩, rfl⟩

/-- **Every method of the compiled domain is one of the three shapes.** -/
theorem parMethodsOf_cases {d : DomDesc} {L : ParCfg} {m : MethodDesc}
    (hm : m ∈ parMethodsOf d L) :
    (m = (parName L, TnDesc.nil) ∧ ∀ xs ∈ L, xs = []) ∨
      (∃ i, i < L.length ∧ ∃ a xs, L.getI i = Sum.inl a :: xs ∧
        m = (parName L, parStepTn a (parName (L.set i xs)))) ∨
      (∃ i, i < L.length ∧ ∃ c xs, L.getI i = Sum.inr c :: xs ∧ ∃ e ∈ d.methods, e.1 = c ∧
        m = (parName L, singleTn (parName (L.set i (TnDesc.seqBody e.2 ++ xs))))) := by
  rw [parMethodsOf, List.mem_append] at hm
  rcases hm with hdone | hstep
  · by_cases hall : L.all (fun xs => xs.isEmpty) = true
    · rw [if_pos hall, List.mem_singleton] at hdone
      refine Or.inl ⟨hdone, ?_⟩
      simp only [List.all_eq_true, List.isEmpty_iff] at hall
      exact fun xs hxs => hall xs hxs
    · rw [if_neg hall] at hdone
      exact absurd hdone (by simp)
  · obtain ⟨i, hi, hmem⟩ := List.mem_flatMap.1 hstep
    have hi' : i < L.length := by simpa using hi
    rw [parStepMethods] at hmem
    rcases hL : L.getI i with _ | ⟨x, xs⟩
    · rw [hL] at hmem
      exact absurd hmem (by simp)
    · rcases x with a | c
      · rw [hL] at hmem
        simp only [List.mem_singleton] at hmem
        exact Or.inr (Or.inl ⟨i, hi', a, xs, hL, hmem⟩)
      · rw [hL] at hmem
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmem
        rw [List.mem_filter] at he
        exact Or.inr (Or.inr ⟨i, hi', c, xs, hL, e, he.1, by simpa using he.2, rfl⟩)

/-! ### The compiled domain is totally ordered and regular -/

theorem singleTn_isTO (c : ℕ) : (singleTn c).toTaskNetwork.IsTotallyOrdered := by
  intro x hx y hy hne
  rw [mem_singleTn_T] at hx hy
  exact absurd (hx.trans hy.symm) hne

theorem singleTn_isRegular (c : ℕ) : (singleTn c).toTaskNetwork.IsRegular := by
  constructor
  · intro x hx y hy _ _
    rw [mem_singleTn_T] at hx hy
    rw [hx, hy]
  · intro x hx _ y hy hne
    rw [mem_singleTn_T] at hx hy
    exact absurd (hy.trans hx.symm) hne

theorem nilTn_T : (TnDesc.nil).toTaskNetwork.T = ∅ := rfl

theorem nilTn_isTO : (TnDesc.nil).toTaskNetwork.IsTotallyOrdered := by
  intro x hx
  rw [nilTn_T] at hx
  exact absurd hx (by simp)

theorem nilTn_isRegular : (TnDesc.nil).toTaskNetwork.IsRegular := by
  constructor
  · intro x hx
    rw [nilTn_T] at hx
    exact absurd hx (by simp)
  · intro x hx
    rw [nilTn_T] at hx
    exact absurd hx (by simp)

/-- **The compiled domain is totally ordered.** -/
theorem parDom_methodsTO (k : ℕ) (d : DomDesc) : (parDom k d).MethodsTO := by
  intro e he
  obtain ⟨L, -, hmem⟩ := mem_parMethods_iff.1 he
  rcases parMethodsOf_cases hmem with ⟨rfl, -⟩ | ⟨i, -, a, xs, -, rfl⟩ | ⟨i, -, c, xs, -, e', -, -, rfl⟩
  · exact nilTn_isTO
  · exact parStepTn_isTO _ _
  · exact singleTn_isTO _

/-- **The compiled domain is regular.** -/
theorem parDom_methodsReg (k : ℕ) (d : DomDesc) : (parDom k d).MethodsReg := by
  intro e he
  obtain ⟨L, -, hmem⟩ := mem_parMethods_iff.1 he
  rcases parMethodsOf_cases hmem with ⟨rfl, -⟩ | ⟨i, -, a, xs, -, rfl⟩ | ⟨i, -, c, xs, -, e', -, -, rfl⟩
  · exact nilTn_isRegular
  · exact parStepTn_isRegular _ _
  · exact singleTn_isRegular _

/-! ### The source class: an unordered initial network of at most `k` tasks -/

namespace InstDesc

/-- **The initial task network is an unordered network of at most `k` compound tasks**: it is
described as the network of its own compound names, with no ordering pairs at all, and there are
at most `k` of them. -/
def IsParLe (k : ℕ) (q : InstDesc) : Prop :=
  q.tnI = netTn q.tnI.compoundNames [] ∧ q.tnI.compoundNames.length ≤ k

/-- The condition is monotone in the bound. -/
theorem IsParLe.mono {k k' : ℕ} {q : InstDesc} (hk : k ≤ k') (h : q.IsParLe k) : q.IsParLe k' :=
  ⟨h.1, h.2.trans hk⟩

/-- An unordered network of at most `k` tasks is in particular a network of at most `k` tasks. -/
theorem IsParLe.isNetLe {k : ℕ} {q : InstDesc} (h : q.IsParLe k) : q.IsNetLe k := by
  have hord : q.tnI.ordList = [] := by rw [h.1]; rfl
  refine ⟨by rw [hord]; exact h.1, h.2, ?_⟩
  rw [hord]
  exact nil_mem_ordEnum _

/-- **The canonical rooted instances are unordered networks of one task**, so the class of
unordered networks of at most `k ≥ 1` tasks contains the planning problems of the draft paper. -/
theorem isParLe_one_of_singleTn (I G : List ℕ) (c : ℕ) :
    InstDesc.IsParLe 1 ((I, G, singleTn c) : InstDesc) := by
  have h : (InstDesc.tnI ((I, G, singleTn c) : InstDesc)) = netTn [c] [] := rfl
  constructor
  · rw [h, netTn_compoundNames]
  · rw [h, netTn_compoundNames]
    simp

end InstDesc

/-! ### The initial configuration -/

/-- The configuration the compiled instance starts from: one process per initial task. -/
theorem mem_parCfgs_initCfg {k : ℕ} {d : DomDesc} {ws : List ℕ} (hlen : ws.length ≤ k)
    (hall : ∀ c ∈ ws, c ∈ d.heads) : (ws.map fun c => [Sum.inr c]) ∈ parCfgs k d := by
  rw [parCfgs, mem_parTuplesLe]
  refine ⟨by simpa using hlen, ?_⟩
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  exact mem_parEntries_head (hall c hc)

/-- If the initial configuration is not a configuration of the compiled domain then the initial
network names a compound task the source domain never decomposes. -/
theorem exists_dead_of_notMem_parCfgs {k : ℕ} {d : DomDesc} {ws : List ℕ} (hlen : ws.length ≤ k)
    (h : (ws.map fun c => [Sum.inr c]) ∉ parCfgs k d) : ∃ c ∈ ws, c ∉ d.heads := by
  by_contra hcon
  push_neg at hcon
  exact h (mem_parCfgs_initCfg hlen hcon)

/-- Every method of the compiled domain for `L` decomposes the name of `L`. -/
theorem parMethodsOf_fst {d : DomDesc} {L : ParCfg} {m : MethodDesc}
    (hm : m ∈ parMethodsOf d L) : m.1 = parName L := by
  rcases parMethodsOf_cases hm with ⟨rfl, -⟩ | ⟨i, -, a, xs, -, rfl⟩ | ⟨i, -, c, xs, -, e, -, -, rfl⟩ <;>
    rfl

/-- The compiled domain only decomposes names of its configurations. -/
theorem mem_parCfgs_of_mem_heads {k : ℕ} {d : DomDesc} {L : ParCfg}
    (h : parName L ∈ (parDom k d).heads) : L ∈ parCfgs k d := by
  obtain ⟨m, hm, hm1⟩ := mem_heads_iff.1 h
  obtain ⟨L', hL', hmem⟩ := mem_parMethods_iff.1 hm
  have : parName L' = parName L := by rw [← parMethodsOf_fst hmem, hm1]
  exact parName_inj.1 this ▸ hL'


end Syn

end HTN
