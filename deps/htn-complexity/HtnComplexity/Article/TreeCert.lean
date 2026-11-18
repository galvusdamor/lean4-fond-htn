import HtnComplexity.Article.StripsAcyc
import HtnComplexity.PolyInst.Enum
/-!
# Certificates of decomposition trees

A plan of an HTN problem is certified by decomposition trees whose yields merge into the plan
(Prop. 2.2.1, `HTN.Article.Problem.solvable_iff_trees`).  This file fixes a *flat* encoding of
such trees as a list of nodes, the **tree certificate** `HTN.Article.TCert`, and a Boolean check
of it (`HTN.Article.certB`) on a problem description.

A node (`HTN.Article.NodeC`) records its label (a primitive or compound task name), for a compound
node the index of the method decomposing it, the map from the task ids of the method's network to
the nodes of the children (`kids`, children *precede* their parent in the list), its yield `ys`,
and the witness `w` of the ordered merge of the children's yields (Def. 2.10).  The certificate
adds the map from the ids of the initial task network to their trees, the plan, and the witness
of the merge at the root.

* **`HTN.Article.treesYield_of_certB`** — soundness: from a certificate passing the check, valid
  decomposition trees for the initial task network whose yields merge into the plan
  (`HTN.Article.treeF`, by recursion along the list).
-/

namespace HTN

namespace Article

open Syn Syn.PolyInst

/-- A node of a tree certificate: label, method index, children, yield, merge witness. -/
abbrev NodeC : Type := (Bool × ℕ) × ℕ × List (ℕ × ℕ) × List ℕ × List (ℕ × ℕ)

namespace NodeC

/-- The label: `(true, c)` a compound task `c`, `(false, a)` a primitive task `a`. -/
def lbl (v : NodeC) : Bool × ℕ := v.1
/-- The index of the decomposing method. -/
def mi (v : NodeC) : ℕ := v.2.1
/-- The children: task id of the method's network ↦ node index. -/
def kids (v : NodeC) : List (ℕ × ℕ) := v.2.2.1
/-- The yield. -/
def ys (v : NodeC) : List ℕ := v.2.2.2.1
/-- The witness of the ordered merge of the children's yields. -/
def w (v : NodeC) : List (ℕ × ℕ) := v.2.2.2.2

end NodeC

/-- **A tree certificate**: the nodes, the map from the ids of `tn_I` to nodes, the plan and the
witness of the merge at the root. -/
abbrev TCert : Type := List NodeC × List (ℕ × ℕ) × List ℕ × List (ℕ × ℕ)

/-- The raw label of an id in a network description. -/
def lblOf (t : TnDesc) (x : ℕ) : Bool × ℕ := (t.lbl.lookup x).getD (false, 0)

/-- A raw label as a task name. -/
def toSum (l : Bool × ℕ) : ℕ ⊕ ℕ := if l.1 then Sum.inr l.2 else Sum.inl l.2

theorem label_eq_toSum (t : TnDesc) (x : ℕ) : t.label x = toSum (lblOf t x) := by
  unfold TnDesc.label lblOf toSum
  rcases t.lbl.lookup x with _ | ⟨_ | _, n⟩ <;> rfl

/-- `R` holds between every entry and every later entry. -/
def pairwiseB {β : Type} (R : β → β → Bool) (l : List β) : Bool :=
  (splits l).all fun q => q.2.2.all (R q.2.1)

theorem pairwiseB_iff {β : Type} (R : β → β → Bool) (l : List β) :
    pairwiseB R l = true ↔ l.Pairwise fun a b => R a b = true := by
  unfold pairwiseB
  rw [List.all_eq_true]
  induction l with
  | nil => simp [splits]
  | cons a l ih =>
    simp only [splits, List.mem_cons, List.mem_map, forall_eq_or_imp, List.pairwise_cons,
      List.all_eq_true, forall_exists_index, and_imp]
    rw [← ih]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun q hq => List.all_eq_true.2 (h2 (a :: q.1, q.2.1, q.2.2) q hq rfl)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun _ q hq e => e ▸ List.all_eq_true.1 (h2 q hq)⟩

/-- The child of an id. -/
def kidOf (kids : List (ℕ × ℕ)) (x : ℕ) : ℕ := (kids.lookup x).getD 0

/-- **The ordered merge** of the yields `ysx` of the ids of `t` into `ys`, witnessed by `w`. -/
def mergeB (t : TnDesc) (ysx : ℕ → List ℕ) (ys : List ℕ) (w : List (ℕ × ℕ)) : Bool :=
  (w.map Prod.snd == ys) && w.all (fun e => decide (e.1 ∈ t.ids)) &&
    t.ids.all (fun x => (w.filter fun e => e.1 == x).map Prod.snd == ysx x) &&
    pairwiseB (fun e e' => !decide ((e'.1, e.1) ∈ t.ordList)) w

/-- **The children of a node**: every id of `t` has a child, which precedes `j` and carries the
id's label. -/
def kidsB (nodes : List NodeC) (j : ℕ) (t : TnDesc) (kids : List (ℕ × ℕ)) : Bool :=
  t.ids.all (fun x => decide (x ∈ kids.map Prod.fst)) &&
    kids.all fun e => decide (e.2 < j) && decide ((nodes.getI e.2).lbl = lblOf t e.1)

/-- **The check of the node `j`.** -/
def nodeB (p : ProbDesc) (nodes : List NodeC) (j : ℕ) : Bool :=
  let v := nodes.getI j
  if v.lbl.1 then
    decide (v.mi < p.methods.length) && ((p.methods.getI v.mi).1 == v.lbl.2) &&
      kidsB nodes j (p.methods.getI v.mi).2 v.kids &&
      mergeB (p.methods.getI v.mi).2 (fun x => (nodes.getI (kidOf v.kids x)).ys) v.ys v.w
  else v.ys == [v.lbl.2]

/-- **The check of a certificate**: all nodes, and the merge at the root. -/
def certB (p : ProbDesc) (c : TCert) : Bool :=
  (List.range c.1.length).all (fun j => nodeB p c.1 j) &&
    kidsB c.1 c.1.length p.tnI c.2.1 &&
    mergeB p.tnI (fun x => (c.1.getI (kidOf c.2.1 x)).ys) c.2.2.1 c.2.2.2

/-! ### Soundness -/

/-- The tree of node `j`, with fuel. -/
def treeF (p : ProbDesc) (nodes : List NodeC) : ℕ → ℕ → DTree ℕ ℕ ℕ
  | 0, _ => .leaf 0
  | n + 1, j =>
    let v := nodes.getI j
    if v.lbl.1 then
      .node v.lbl.2 (MethodDesc.toMethod (p.methods.getI v.mi))
        (fun x => treeF p nodes n (kidOf v.kids x))
    else .leaf v.lbl.2

theorem lookup_of_mem_map_fst {l : List (ℕ × ℕ)} {x : ℕ} (h : x ∈ l.map Prod.fst) :
    (x, kidOf l x) ∈ l := by
  unfold kidOf
  rcases hl : l.lookup x with _ | k
  · exfalso
    obtain ⟨⟨y, k⟩, hm, rfl⟩ := List.mem_map.1 h
    rw [List.lookup_eq_none_iff] at hl
    exact absurd (hl _ hm) (by simp)
  · exact mem_of_lookup_eq_some hl

/-- The merge check gives the ordered merge, for a well-formed network. -/
theorem ordMerge_of_mergeB {prim : ℕ → Prop} {t : TnDesc} (ht : TnValid prim t)
    {ysx : ℕ → List ℕ} {ys : List ℕ} {w : List (ℕ × ℕ)} (h : mergeB t ysx ys w = true) :
    OrdMerge t.toTaskNetwork ysx ys := by
  unfold mergeB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨w, h1, fun e he => by simpa [TnDesc.toTaskNetwork] using h2 e he, fun x hx => ?_, ?_⟩
  · have hx' : x ∈ t.ids := by simpa [TnDesc.toTaskNetwork] using hx
    have := h3 x hx'
    simpa [beq_iff_eq] using this
  · refine ((pairwiseB_iff _ _).1 h4).imp fun {e e'} he hord => ?_
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at he
    exact he ((ht.ordOf_iff).1 hord)

/-- **The trees of a certificate are valid and yield the recorded yields.** -/
theorem treeF_spec {p : ProbDesc} (hp : p.Valid) {nodes : List NodeC}
    (hn : ∀ j < nodes.length, nodeB p nodes j = true) :
    ∀ n j, j < n → j < nodes.length →
      (treeF p nodes n j).Valid p.toProblem.methods (toSum (nodes.getI j).lbl) ∧
        (treeF p nodes n j).Yield (nodes.getI j).ys := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj hjl
    have hnj := hn j hjl
    unfold nodeB at hnj
    simp only [treeF]
    by_cases hc : (nodes.getI j).lbl.1 = true
    · rw [if_pos hc] at hnj ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hnj
      obtain ⟨⟨⟨hmi, hhead⟩, hkids⟩, hmerge⟩ := hnj
      set v := nodes.getI j
      set e := p.methods.getI v.mi
      have he : e ∈ p.methods := by
        simp only [e, List.getI_eq_getElem _ hmi]; exact List.getElem_mem _
      have hvalid : TnValid p.Declared e.2 := hp.methods e he
      unfold kidsB at hkids
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hkids
      obtain ⟨hcov, hk⟩ := hkids
      -- the children
      have hchild : ∀ x ∈ e.2.ids, kidOf v.kids x < j ∧
          (nodes.getI (kidOf v.kids x)).lbl = lblOf e.2 x := by
        intro x hx
        have := hk _ (lookup_of_mem_map_fst (hcov x hx))
        exact this
      have hsum : toSum v.lbl = Sum.inr v.lbl.2 := by simp [toSum, hc]
      rw [hsum]
      refine ⟨.node ⟨e, he, rfl⟩ hhead (fun x hx => ?_), .node _ (fun x hx => ?_)
        (ordMerge_of_mergeB hvalid hmerge)⟩
      · have hx' : x ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hx
        obtain ⟨hlt, hlbl⟩ := hchild x hx'
        have := (ih (kidOf v.kids x) (by omega) (by omega)).1
        rw [hlbl] at this
        simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork, label_eq_toSum] using this
      · have hx' : x ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hx
        obtain ⟨hlt, -⟩ := hchild x hx'
        exact (ih (kidOf v.kids x) (by omega) (by omega)).2
    · rw [if_neg hc] at hnj ⊢
      simp only [beq_iff_eq] at hnj
      have hsum : toSum (nodes.getI j).lbl = Sum.inl (nodes.getI j).lbl.2 := by
        simp [toSum, hc]
      rw [hsum, hnj]
      exact ⟨.leaf _, .leaf _⟩

/-- **Soundness of tree certificates.** -/
theorem treesYield_of_certB {p : ProbDesc} (hp : p.Valid) {c : TCert} (h : certB p c = true) :
    ∃ trees, TreesYield p.toProblem.methods p.toProblem.tnI trees c.2.2.1 := by
  unfold certB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨hn, hroots⟩, hmerge⟩ := h
  unfold kidsB at hroots
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hroots
  obtain ⟨hcov, hk⟩ := hroots
  have hchild : ∀ x ∈ p.tnI.ids, kidOf c.2.1 x < c.1.length ∧
      (c.1.getI (kidOf c.2.1 x)).lbl = lblOf p.tnI x := fun x hx =>
    hk _ (lookup_of_mem_map_fst (hcov x hx))
  refine ⟨fun x => treeF p c.1 c.1.length (kidOf c.2.1 x), fun x hx => ?_,
    fun x => (c.1.getI (kidOf c.2.1 x)).ys, fun x hx => ?_, ordMerge_of_mergeB hp.tnI hmerge⟩
  · have hx' : x ∈ p.tnI.ids := by simpa [ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx
    obtain ⟨hlt, hlbl⟩ := hchild x hx'
    have := (treeF_spec hp hn c.1.length _ hlt hlt).1
    rw [hlbl] at this
    simpa [ProbDesc.toProblem, TnDesc.toTaskNetwork, label_eq_toSum] using this
  · have hx' : x ∈ p.tnI.ids := by simpa [ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx
    obtain ⟨hlt, -⟩ := hchild x hx'
    exact (treeF_spec hp hn c.1.length _ hlt hlt).2

end Article

end HTN
