import HtnComplexity.Computable.ChainTn
/-!
# Arbitrary *bounded* initial task networks, and the rooting of one

`HtnComplexity/Computable/ChainTn.lean` prepares the rooting of an initial task network
that is a **chain** of at most `k` compound tasks.  A chain is a totally ordered network, which
is all a source instance of a totally ordered class can carry; a partially ordered class,
however, admits an arbitrary ordering of the initial tasks, and that is what this file prepares.

* `HTN.Syn.netTn ws ord` — the described network with one compound task per entry of `ws`,
  identified by its position, and the ordering pairs `ord`;
* `HTN.Syn.subseqs`, `HTN.Syn.posPairs`, `HTN.Syn.ordEnum` — the sublists of a list, the pairs of
  positions below `n`, and the orderings over `n` tasks in canonical form; every ordering of the
  `n` tasks occurs (`HTN.Syn.mem_ordEnum_iff`), and there are `2 ^ (n * n)` of them;
* `HTN.Syn.InstDesc.IsNetLe k q` — the source condition: the initial task network of `q` is the
  described network of its own compound names and its own — canonically listed — ordering
  pairs, and there are at most `k` tasks;
* the two translations `HTN.Syn.netRootDom`, `HTN.Syn.netRootInst`.

The correctness of the rooting is `HtnCompilability/Computable/NetRoot.lean`.
-/

namespace HTN

namespace Syn

/-! ### Looking a label up in a canonically labelled list -/

/-- Looking up an entry of a list of pairs built from the identifier itself. -/
theorem lookup_map_self {β : Type} (f : ℕ → β) :
    ∀ {l : List ℕ} {i : ℕ}, i ∈ l → (l.map fun j => (j, f j)).lookup i = some (f i)
  | [], i, hi => by simp at hi
  | a :: l, i, hi => by
    rw [List.map_cons, List.lookup_cons]
    by_cases h : i = a
    · subst h; simp
    · have hb : (i == a) = false := by simpa using h
      rw [hb]
      exact lookup_map_self f ((List.mem_cons.1 hi).resolve_left h)

/-! ### The described network of a list of names and a list of ordering pairs -/

/-- **The described task network of the compound names `ws` and the ordering pairs `ord`**: one
task per entry of `ws`, identified by its position. -/
def netTn (ws : List ℕ) (ord : List (ℕ × ℕ)) : TnDesc :=
  (List.range ws.length, ord, (List.range ws.length).map fun i => (i, true, ws.getD i 0))

@[simp] lemma netTn_ids (ws : List ℕ) (ord : List (ℕ × ℕ)) :
    (netTn ws ord).ids = List.range ws.length := rfl

@[simp] lemma netTn_ordList (ws : List ℕ) (ord : List (ℕ × ℕ)) :
    (netTn ws ord).ordList = ord := rfl

@[simp] lemma netTn_lbl (ws : List ℕ) (ord : List (ℕ × ℕ)) :
    (netTn ws ord).lbl = (List.range ws.length).map fun i => (i, true, ws.getD i 0) := rfl

lemma netTn_labelList (ws : List ℕ) (ord : List (ℕ × ℕ)) {i : ℕ} (hi : i < ws.length) :
    TnDesc.labelList true (netTn ws ord).lbl i = [ws.getD i 0] := by
  have hmem : i ∈ List.range ws.length := by simpa using hi
  have hlk := lookup_map_self (fun j => ((true, ws.getD j 0) : Bool × ℕ)) hmem
  rw [TnDesc.labelList_eq, netTn_lbl, hlk]
  simp

/-- The compound names of the described network are its entries. -/
@[simp] theorem netTn_compoundNames (ws : List ℕ) (ord : List (ℕ × ℕ)) :
    (netTn ws ord).compoundNames = ws := by
  rw [TnDesc.compoundNames, netTn_ids]
  have h : ((List.range ws.length).flatMap fun i =>
      TnDesc.labelList true (netTn ws ord).lbl i) =
      (List.range ws.length).flatMap fun i => [ws.getD i 0] :=
    List.flatMap_congr fun i hi => netTn_labelList ws ord (by simpa using hi)
  have hfm : ∀ (l : List ℕ) (f : ℕ → ℕ), (l.flatMap fun j => [f j]) = l.map f := by
    intro l f
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  rw [h, hfm]
  exact List.ext_getElem (by simp) fun n h1 h2 => by
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ h2]

/-- Renaming the compound names of a described network renames its entries. -/
theorem renameC_netTn (σ : ℕ → ℕ) (ws : List ℕ) (ord : List (ℕ × ℕ)) :
    (netTn ws ord).renameC σ = netTn (ws.map σ) ord := by
  have hlen : (ws.map σ).length = ws.length := by simp
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (netTn ws ord).ids = (netTn (ws.map σ) ord).ids
    rw [netTn_ids, netTn_ids, hlen]
  · show (netTn ws ord).ordList = (netTn (ws.map σ) ord).ordList
    rfl
  · show ((netTn ws ord).renameC σ).lbl = (netTn (ws.map σ) ord).lbl
    rw [TnDesc.renameC_lbl, netTn_lbl, netTn_lbl, hlen, List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < ws.length := by simpa using hi
    simp only [Function.comp_apply, if_pos]
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ (by simpa using hi')]
    simp

/-- The size of a described network. -/
theorem size_netTn_le (ws : List ℕ) (ord : List (ℕ × ℕ)) :
    (netTn ws ord).size ≤ 2 * ws.length + ord.length := by
  rw [TnDesc.size, netTn_ids, netTn_lbl, netTn_ordList]
  simp only [List.length_range, List.length_map]
  omega

/-- A one-task network with no ordering pair is the canonical single-task network. -/
@[simp] theorem netTn_singleton (c : ℕ) : netTn [c] [] = singleTn c := rfl

/-! ### The sublists of a list -/

/-- The sublists of a list, as a `foldr` — which is what makes it primitive recursive. -/
def subseqs {α : Type} (l : List α) : List (List α) :=
  l.foldr (fun a r => r.flatMap fun s => [s, a :: s]) [[]]

@[simp] lemma subseqs_nil {α : Type} : subseqs ([] : List α) = [[]] := rfl

lemma subseqs_cons {α : Type} (a : α) (l : List α) :
    subseqs (a :: l) = (subseqs l).flatMap fun s => [s, a :: s] := rfl

theorem mem_subseqs_iff {α : Type} {l s : List α} : s ∈ subseqs l ↔ s.Sublist l := by
  induction l generalizing s with
  | nil =>
    simp only [subseqs_nil, List.mem_singleton, List.sublist_nil]
  | cons a l ih =>
    simp only [subseqs_cons, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, ih]
    constructor
    · rintro ⟨t, ht, rfl | rfl⟩
      · exact ht.trans (List.sublist_cons_self a l)
      · exact ht.cons₂ a
    · intro h
      rcases List.sublist_cons_iff.1 h with h | ⟨r, rfl, hr⟩
      · exact ⟨s, h, Or.inl rfl⟩
      · exact ⟨r, hr, Or.inr rfl⟩

theorem length_subseqs {α : Type} (l : List α) : (subseqs l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [subseqs_cons, List.length_flatMap]
    have h : ((subseqs l).map fun s => ([s, a :: s]).length) =
        List.replicate (subseqs l).length 2 := by
      simp [List.map_const']
    rw [h, List.sum_replicate, ih, List.length_cons, pow_succ]
    simp [Nat.mul_comm]

/-! ### The orderings over `n` tasks -/

/-- The pairs of positions below `n`. -/
def posPairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun a => (List.range n).map fun b => (a, b)

theorem length_posPairs (n : ℕ) : (posPairs n).length = n * n := by
  rw [posPairs, List.length_flatMap]
  simp

theorem mem_posPairs {n : ℕ} {p : ℕ × ℕ} : p ∈ posPairs n ↔ p.1 < n ∧ p.2 < n := by
  simp only [posPairs, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p.1, h1, p.2, h2, rfl⟩

/-- **The orderings over `n` tasks, in canonical form**: the sublists of the list of all pairs of
positions below `n`. -/
def ordEnum (n : ℕ) : List (List (ℕ × ℕ)) := subseqs (posPairs n)

/-- Every ordering of `n` tasks occurs in the enumeration, namely as the sublist of the canonical
list of pairs it selects. -/
theorem mem_ordEnum_iff {n : ℕ} {ord : List (ℕ × ℕ)} :
    ord ∈ ordEnum n ↔ ord.Sublist (posPairs n) := mem_subseqs_iff

theorem length_ordEnum (n : ℕ) : (ordEnum n).length = 2 ^ (n * n) := by
  rw [ordEnum, length_subseqs, length_posPairs]

/-- An ordering of the enumeration is short. -/
theorem length_le_of_mem_ordEnum {n : ℕ} {ord : List (ℕ × ℕ)} (h : ord ∈ ordEnum n) :
    ord.length ≤ n * n := by
  have := (mem_ordEnum_iff.1 h).length_le
  rwa [length_posPairs] at this

/-- The empty ordering is one of the enumerated ones. -/
@[simp] theorem nil_mem_ordEnum (n : ℕ) : [] ∈ ordEnum n :=
  mem_ordEnum_iff.2 (List.nil_sublist _)

/-! ### The source condition -/

namespace InstDesc

/-- **The initial task network is an arbitrary network of at most `k` compound tasks**: it is
described as the network of its own compound names and its own ordering pairs, the tasks are
identified by their positions, and the ordering pairs are listed canonically. -/
def IsNetLe (k : ℕ) (q : InstDesc) : Prop :=
  q.tnI = netTn q.tnI.compoundNames q.tnI.ordList ∧
    q.tnI.compoundNames.length ≤ k ∧
    q.tnI.ordList ∈ ordEnum q.tnI.compoundNames.length

/-- The condition is monotone in the bound. -/
theorem IsNetLe.mono {k k' : ℕ} {q : InstDesc} (hk : k ≤ k') (h : q.IsNetLe k) :
    q.IsNetLe k' :=
  ⟨h.1, h.2.1.trans hk, h.2.2⟩

/-- **The canonical rooted instances are networks of one task**, so the class of networks of at
most `k ≥ 1` tasks contains the planning problems of the draft paper. -/
theorem isNetLe_one_of_singleTn (I G : List ℕ) (c : ℕ) :
    InstDesc.IsNetLe 1 ((I, G, singleTn c) : InstDesc) := by
  have h : (InstDesc.tnI ((I, G, singleTn c) : InstDesc)) = netTn [c] [] := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [h, netTn_compoundNames, netTn_ordList]
  · rw [h, netTn_compoundNames]; simp
  · rw [h, netTn_compoundNames, netTn_ordList]
    exact nil_mem_ordEnum _

end InstDesc

/-! ### The two translations -/

/-- The fresh compound name of the network `(ws, ord)`: an even number, and injectively so. -/
def netRootName (p : List ℕ × List (ℕ × ℕ)) : ℕ := 2 * Encodable.encode p

theorem netRootName_injective : Function.Injective netRootName := by
  intro x y h
  simpa [netRootName, Encodable.encode_inj] using h

theorem oddName_ne_netRootName (n : ℕ) (p : List ℕ × List (ℕ × ℕ)) :
    oddName n ≠ netRootName p := by
  simp only [oddName, netRootName]
  omega

/-- The fresh methods: one per network of at most `k` compound names of the domain. -/
def netRootMethods (k : ℕ) (d : DomDesc) : List MethodDesc :=
  (tuplesLe k d.heads).flatMap fun ws =>
    (ordEnum ws.length).map fun ord => (netRootName (ws, ord), netTn (ws.map oddName) ord)

theorem mem_netRootMethods {k : ℕ} {d : DomDesc} {p : MethodDesc} :
    p ∈ netRootMethods k d ↔ ∃ ws ∈ tuplesLe k d.heads, ∃ ord ∈ ordEnum ws.length,
      p = (netRootName (ws, ord), netTn (ws.map oddName) ord) := by
  simp only [netRootMethods, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨ws, hws, ord, hord, rfl⟩
    exact ⟨ws, hws, ord, hord, rfl⟩
  · rintro ⟨ws, hws, ord, hord, rfl⟩
    exact ⟨ws, hws, ord, hord, rfl⟩

/-- **The compiled domain description**: the source domain with its compound names moved out of
the way, plus one method per network of at most `k` of them. -/
def netRootDom (k : ℕ) (d : DomDesc) : DomDesc :=
  addRootsDom (netRootMethods k d) (d.renameC oddName)

/-- **The compiled instance description**: the initial task network is the single fresh task of
the source's network. -/
def netRootInst (q : InstDesc) : InstDesc :=
  (q.initList, q.goalList, singleTn (netRootName (q.tnI.compoundNames, q.tnI.ordList)))

end Syn

end HTN
