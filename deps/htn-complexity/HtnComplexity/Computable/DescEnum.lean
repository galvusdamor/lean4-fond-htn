import HtnPlanning.Computable.Names
import HtnPlanning.Core.ListsUpTo
/-!
# Enumerating the descriptions of bounded size over a fixed pool of names

A domain description of syntactic size at most `s` whose names all come from a list `P` is one
of finitely many, and this file writes that list down:

* `HTN.Syn.domsUpTo P s` — all domain descriptions of size at most `s` over the names of `P`
  (and possibly some more);
* `HTN.Syn.mem_domsUpTo` — every description of size at most `s` whose names lie in `P` is
  listed;
* `HTN.Syn.length_domsUpTo_le` — there are at most `(|P| + 2) ^ (16 * (s + 1) ^ 2)` of them.

Together with the equivariance of the semantics
(`HtnPlanning/Computable/Rename.lean`) this is what bounds the number of solvability
behaviours a description of bounded size can have on a finite family of instances.
-/

namespace HTN

namespace Syn

/-- The ordering pairs over a pool of names. -/
def pairsOver (P : List ℕ) : List (ℕ × ℕ) := P.flatMap fun a => P.map fun b => (a, b)

/-- The labels over a pool of names. -/
def lblsOver (P : List ℕ) : List (ℕ × Bool × ℕ) :=
  P.flatMap fun i => [true, false].flatMap fun b => P.map fun n => (i, b, n)

/-- All described task networks of size at most `s` over the pool `P`. -/
def tnsUpTo (P : List ℕ) (s : ℕ) : List TnDesc :=
  (listsUpTo s P).flatMap fun ids =>
    (listsUpTo s (pairsOver P)).flatMap fun ord =>
      (listsUpTo s (lblsOver P)).map fun lbl => (ids, ord, lbl)

/-- All described actions of size at most `s` over the pool `P`. -/
def actsUpTo (P : List ℕ) (s : ℕ) : List ActionDesc :=
  P.flatMap fun a =>
    (listsUpTo s P).flatMap fun pre =>
      (listsUpTo s P).flatMap fun add =>
        (listsUpTo s P).map fun del => (a, pre, add, del)

/-- All described methods of size at most `s` over the pool `P`. -/
def methsUpTo (P : List ℕ) (s : ℕ) : List MethodDesc :=
  P.flatMap fun c => (tnsUpTo P s).map fun t => (c, t)

/-- All domain descriptions of size at most `s` over the pool `P`. -/
def domsUpTo (P : List ℕ) (s : ℕ) : List DomDesc :=
  (listsUpTo s (actsUpTo P s)).flatMap fun acts =>
    (listsUpTo s (methsUpTo P s)).map fun ms => (acts, ms)

/-! ### Size bookkeeping -/

/-- A list is at most as long as the sum of a family of positive numbers indexed by it. -/
lemma length_le_sum_map {α : Type} (l : List α) (f : α → ℕ) (h : ∀ x ∈ l, 1 ≤ f x) :
    l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

lemma ActionDesc.size_le_of_mem {d : DomDesc} {a : ActionDesc} (ha : a ∈ d.actions) :
    a.size ≤ d.size := by
  have h : a.size ≤ (d.actions.map ActionDesc.size).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem ha)
  simp only [DomDesc.size]
  omega

lemma MethodDesc.size_le_of_mem {d : DomDesc} {m : MethodDesc} (hm : m ∈ d.methods) :
    m.size ≤ d.size := by
  have h : m.size ≤ (d.methods.map MethodDesc.size).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hm)
  simp only [DomDesc.size]
  omega

lemma DomDesc.length_actions_le_size (d : DomDesc) : d.actions.length ≤ d.size := by
  have h := length_le_sum_map d.actions ActionDesc.size fun a _ => by simp only [ActionDesc.size]; omega
  simp only [size]
  omega

lemma DomDesc.length_methods_le_size (d : DomDesc) : d.methods.length ≤ d.size := by
  have h := length_le_sum_map d.methods MethodDesc.size fun m _ => by simp [MethodDesc.size]
  simp only [size]
  omega

/-! ### The enumeration is complete -/

/-- Every described task network of size at most `s` over the pool `P` is listed. -/
theorem mem_tnsUpTo {t : TnDesc} {P : List ℕ} {s : ℕ} (hs : t.size ≤ s)
    (hn : ∀ x ∈ t.names, x ∈ P) : t ∈ tnsUpTo P s := by
  have hids : t.ids ∈ listsUpTo s P :=
    mem_listsUpTo (by simp only [TnDesc.size] at hs; omega)
      fun x hx => hn x (t.ids_subset_names x hx)
  have hord : t.ordList ∈ listsUpTo s (pairsOver P) := by
    refine mem_listsUpTo (by simp only [TnDesc.size] at hs; omega) fun x hx => ?_
    obtain ⟨h1, h2⟩ := t.ordList_subset_names x hx
    refine List.mem_flatMap.2 ⟨x.1, hn _ h1, ?_⟩
    exact List.mem_map.2 ⟨x.2, hn _ h2, rfl⟩
  have hlbl : t.lbl ∈ listsUpTo s (lblsOver P) := by
    refine mem_listsUpTo (by simp only [TnDesc.size] at hs; omega) fun x hx => ?_
    obtain ⟨h1, h2⟩ := t.lbl_subset_names x hx
    refine List.mem_flatMap.2 ⟨x.1, hn _ h1, ?_⟩
    refine List.mem_flatMap.2 ⟨x.2.1, by cases x.2.1 <;> simp, ?_⟩
    exact List.mem_map.2 ⟨x.2.2, hn _ h2, rfl⟩
  refine List.mem_flatMap.2 ⟨t.ids, hids, List.mem_flatMap.2 ⟨t.ordList, hord, ?_⟩⟩
  exact List.mem_map.2 ⟨t.lbl, hlbl, rfl⟩

/-- **Every domain description of size at most `s` over the pool `P` is listed.** -/
theorem mem_domsUpTo {d : DomDesc} {P : List ℕ} {s : ℕ} (hs : d.size ≤ s)
    (hn : ∀ x ∈ d.names, x ∈ P) : d ∈ domsUpTo P s := by
  have hacts : d.actions ∈ listsUpTo s (actsUpTo P s) := by
    refine mem_listsUpTo (le_trans d.length_actions_le_size hs) fun a ha => ?_
    have hsa : a.size ≤ s := le_trans (ActionDesc.size_le_of_mem ha) hs
    have hna : ∀ x ∈ a.names, x ∈ P := fun x hx => hn x (DomDesc.action_names_subset ha x hx)
    have hpre : a.2.1 ∈ listsUpTo s P :=
      mem_listsUpTo (by simp only [ActionDesc.size] at hsa; omega)
        fun x hx => hna x (by simp [ActionDesc.names, hx])
    have hadd : a.2.2.1 ∈ listsUpTo s P :=
      mem_listsUpTo (by simp only [ActionDesc.size] at hsa; omega)
        fun x hx => hna x (by simp [ActionDesc.names, hx])
    have hdel : a.2.2.2 ∈ listsUpTo s P :=
      mem_listsUpTo (by simp only [ActionDesc.size] at hsa; omega)
        fun x hx => hna x (by simp [ActionDesc.names, hx])
    refine List.mem_flatMap.2 ⟨a.1, hna _ (by simp [ActionDesc.names]), ?_⟩
    refine List.mem_flatMap.2 ⟨a.2.1, hpre, List.mem_flatMap.2 ⟨a.2.2.1, hadd, ?_⟩⟩
    exact List.mem_map.2 ⟨a.2.2.2, hdel, rfl⟩
  have hmeths : d.methods ∈ listsUpTo s (methsUpTo P s) := by
    refine mem_listsUpTo (le_trans d.length_methods_le_size hs) fun m hm => ?_
    have hsm : m.size ≤ s := le_trans (MethodDesc.size_le_of_mem hm) hs
    have hnm : ∀ x ∈ m.names, x ∈ P := fun x hx => hn x (DomDesc.method_names_subset hm x hx)
    have htn : m.2 ∈ tnsUpTo P s :=
      mem_tnsUpTo (by simp only [MethodDesc.size] at hsm; omega)
        fun x hx => hnm x (by simp [MethodDesc.names, hx])
    exact List.mem_flatMap.2 ⟨m.1, hnm _ (by simp [MethodDesc.names]),
      List.mem_map.2 ⟨m.2, htn, rfl⟩⟩
  exact List.mem_flatMap.2 ⟨d.actions, hacts, List.mem_map.2 ⟨d.methods, hmeths, rfl⟩⟩

/-- **There are at most `(|P| + 2) ^ (16 * (s + 1) ^ 2)` of them.** -/
theorem length_domsUpTo_le (P : List ℕ) (s : ℕ) :
    (domsUpTo P s).length ≤ (P.length + 2) ^ (16 * (s + 1) ^ 2) := by
  have hw2 : 2 ≤ P.length + 2 := by omega
  set v := P.length with hv
  set w := v + 2 with hw
  -- one more factor of `w` absorbs an increment
  have hsucc : ∀ (X k : ℕ), X ≤ w ^ k → X + 1 ≤ w ^ (k + 1) := by
    intro X k hX
    have h1 : (1:ℕ) ≤ w ^ k := Nat.one_le_pow _ _ (by omega)
    calc X + 1 ≤ w ^ k + w ^ k := by omega
      _ = 2 * w ^ k := by ring
      _ ≤ w * w ^ k := Nat.mul_le_mul_right _ hw2
      _ = w ^ (k + 1) := by ring
  have hL : (listsUpTo s P).length ≤ w ^ s :=
    le_trans (length_listsUpTo_le P s) (Nat.pow_le_pow_left (by omega) s)
  have hpairs : (pairsOver P).length + 1 ≤ w ^ 2 := by
    have h : (pairsOver P).length ≤ v * v :=
      length_flatMap_le _ _ v fun a _ => by simp [hv]
    have : v * v + 1 ≤ w ^ 2 := by
      rw [hw]; ring_nf; omega
    omega
  have hLp : (listsUpTo s (pairsOver P)).length ≤ w ^ (2 * s) := by
    refine le_trans (length_listsUpTo_le _ s) ?_
    calc ((pairsOver P).length + 1) ^ s ≤ (w ^ 2) ^ s := Nat.pow_le_pow_left hpairs s
      _ = w ^ (2 * s) := by rw [← pow_mul]
  have hlbls : (lblsOver P).length + 1 ≤ w ^ 3 := by
    have h : (lblsOver P).length ≤ v * (2 * v) := by
      refine length_flatMap_le _ _ (2 * v) fun a _ => ?_
      refine le_trans (length_flatMap_le _ _ v fun b _ => by simp [hv]) ?_
      simp
    have : v * (2 * v) + 1 ≤ w ^ 3 := by
      rw [hw]; ring_nf; nlinarith [sq_nonneg v]
    omega
  have hLl : (listsUpTo s (lblsOver P)).length ≤ w ^ (3 * s) := by
    refine le_trans (length_listsUpTo_le _ s) ?_
    calc ((lblsOver P).length + 1) ^ s ≤ (w ^ 3) ^ s := Nat.pow_le_pow_left hlbls s
      _ = w ^ (3 * s) := by rw [← pow_mul]
  have hT : (tnsUpTo P s).length ≤ w ^ (6 * s) := by
    have hinner : ∀ ids ∈ listsUpTo s P,
        ((listsUpTo s (pairsOver P)).flatMap fun ord =>
          (listsUpTo s (lblsOver P)).map fun lbl => (ids, ord, lbl)).length
            ≤ w ^ (2 * s) * w ^ (3 * s) := by
      intro ids _
      refine le_trans (length_flatMap_le _ _ (w ^ (3 * s)) fun ord _ => ?_) ?_
      · simpa using hLl
      · exact Nat.mul_le_mul_right _ hLp
    refine le_trans (length_flatMap_le _ _ (w ^ (2 * s) * w ^ (3 * s)) hinner) ?_
    calc (listsUpTo s P).length * (w ^ (2 * s) * w ^ (3 * s))
        ≤ w ^ s * (w ^ (2 * s) * w ^ (3 * s)) := Nat.mul_le_mul_right _ hL
      _ = w ^ (6 * s) := by rw [← pow_add, ← pow_add]; ring_nf
  have hA : (actsUpTo P s).length ≤ w ^ (3 * s + 1) := by
    have hinner : ∀ a ∈ P,
        ((listsUpTo s P).flatMap fun pre => (listsUpTo s P).flatMap fun add =>
          (listsUpTo s P).map fun del => (a, pre, add, del)).length ≤ w ^ s * (w ^ s * w ^ s) := by
      intro a _
      have h1 : ∀ pre ∈ listsUpTo s P,
          ((listsUpTo s P).flatMap fun add =>
            (listsUpTo s P).map fun del => (a, pre, add, del)).length ≤ w ^ s * w ^ s := by
        intro pre _
        refine le_trans (length_flatMap_le _ _ (w ^ s) fun add _ => by simpa using hL) ?_
        exact Nat.mul_le_mul_right _ hL
      refine le_trans (length_flatMap_le _ _ (w ^ s * w ^ s) h1) ?_
      exact Nat.mul_le_mul_right _ hL
    refine le_trans (length_flatMap_le _ _ _ hinner) ?_
    have hvw : v ≤ w := by omega
    calc P.length * (w ^ s * (w ^ s * w ^ s)) ≤ w * (w ^ s * (w ^ s * w ^ s)) :=
          Nat.mul_le_mul_right _ hvw
      _ = w ^ (3 * s + 1) := by rw [← pow_add, ← pow_add, ← pow_succ']; ring_nf
  have hM : (methsUpTo P s).length ≤ w ^ (6 * s + 1) := by
    refine le_trans (length_flatMap_le _ _ (w ^ (6 * s)) fun c _ => by simpa using hT) ?_
    have hvw : v ≤ w := by omega
    calc P.length * w ^ (6 * s) ≤ w * w ^ (6 * s) := Nat.mul_le_mul_right _ hvw
      _ = w ^ (6 * s + 1) := by rw [← pow_succ']
  have hLA : (listsUpTo s (actsUpTo P s)).length ≤ w ^ ((3 * s + 2) * s) := by
    refine le_trans (length_listsUpTo_le _ s) ?_
    calc ((actsUpTo P s).length + 1) ^ s ≤ (w ^ (3 * s + 2)) ^ s :=
          Nat.pow_le_pow_left (hsucc _ _ hA) s
      _ = w ^ ((3 * s + 2) * s) := by rw [← pow_mul]
  have hLM : (listsUpTo s (methsUpTo P s)).length ≤ w ^ ((6 * s + 2) * s) := by
    refine le_trans (length_listsUpTo_le _ s) ?_
    calc ((methsUpTo P s).length + 1) ^ s ≤ (w ^ (6 * s + 2)) ^ s :=
          Nat.pow_le_pow_left (hsucc _ _ hM) s
      _ = w ^ ((6 * s + 2) * s) := by rw [← pow_mul]
  refine le_trans (length_flatMap_le _ _ (w ^ ((6 * s + 2) * s)) fun acts _ => by
    simpa using hLM) ?_
  calc (listsUpTo s (actsUpTo P s)).length * w ^ ((6 * s + 2) * s)
      ≤ w ^ ((3 * s + 2) * s) * w ^ ((6 * s + 2) * s) := Nat.mul_le_mul_right _ hLA
    _ = w ^ ((3 * s + 2) * s + (6 * s + 2) * s) := by rw [← pow_add]
    _ ≤ w ^ (16 * (s + 1) ^ 2) := by
        refine Nat.pow_le_pow_right (by omega) ?_
        nlinarith [sq_nonneg s]

end Syn

end HTN
