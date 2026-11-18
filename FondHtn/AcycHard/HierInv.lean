import FondHtn.AcycHard.Hier
import FondHtn.PCP.Decomp
/-!
# Single-method hierarchies of chains

A *hierarchy specification* `FOND.AcycHard.HSpec` gives every compound name one body, either a
sequence (*seq-kind*: primitive tasks and seq-kind compound tasks, totally ordered) or a set
(*set-kind*: no order), and a rank that decreases along bodies (acyclicity).

* `FOND.AcycHard.HSpec.exI` — the expansion of a seq-kind item into a list of primitive labels;
  `exMI` the expansion of an item standing alone into a multiset of chains; `exC` the expansion
  of a chain;
* `FOND.AcycHard.HInv` — **the invariant**: the network is a union of chains (`UC`), set-kind
  compound tasks only form pool chains of their own, and the expansions of the control chain and
  of the pool chains are fixed;
* `FOND.AcycHard.HInv.step` — decomposition steps preserve the invariant.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

open HTN

/-- **A hierarchy specification.** -/
structure HSpec (A C : Type) where
  body : C → List (A ⊕ C)
  isSet : C → Bool
  rk : C → ℕ
  rk_lt : ∀ c d, Sum.inr d ∈ body c → rk d < rk c
  seq_items : ∀ c, isSet c = false → ∀ d, Sum.inr d ∈ body c → isSet d = false

namespace HSpec

variable {A C : Type} (H : HSpec A C)

/-- The rank of an item. -/
def itemRk : A ⊕ C → ℕ
  | .inl _ => 0
  | .inr c => H.rk c + 1

theorem itemRk_lt {c : C} {x : A ⊕ C} (h : x ∈ H.body c) : H.itemRk x < H.itemRk (.inr c) := by
  cases x with
  | inl a => simp [itemRk]
  | inr d => have := H.rk_lt c d h; simp [itemRk]; omega

/-- **The expansion of a seq-kind item.** -/
def exI : A ⊕ C → List A
  | .inl a => [a]
  | .inr c => (H.body c).attach.flatMap fun x => exI x.1
termination_by x => H.itemRk x
decreasing_by exact H.itemRk_lt x.2

theorem exI_inl (a : A) : H.exI (.inl a) = [a] := by rw [exI]

theorem exI_inr (c : C) : H.exI (.inr c) = (H.body c).flatMap H.exI := by
  rw [exI]
  conv_rhs => rw [← List.attach_map_subtype_val (H.body c)]
  rw [List.flatMap_map]

/-- A nonempty list as a chain. -/
def filt (l : List A) : Multiset (List A) := if l = [] then 0 else {l}

/-- **The expansion of an item standing alone**: the multiset of its chains. -/
def exMI : A ⊕ C → Multiset (List A)
  | .inl a => {[a]}
  | .inr c => if H.isSet c then ((H.body c).attach.map fun x => exMI x.1).sum
      else filt (H.exI (.inr c))
termination_by x => H.itemRk x
decreasing_by exact H.itemRk_lt x.2

theorem exMI_inl (a : A) : H.exMI (.inl a) = {[a]} := by rw [exMI]

theorem exMI_set {c : C} (h : H.isSet c = true) : H.exMI (.inr c) = ((H.body c).map H.exMI).sum := by
  rw [exMI, if_pos h]
  conv_rhs => rw [← List.attach_map_subtype_val (H.body c)]
  rw [List.map_map]; rfl

theorem exMI_seq {c : C} (h : H.isSet c = false) : H.exMI (.inr c) = filt (H.exI (.inr c)) := by
  rw [exMI, if_neg (by simp [h])]

/-- Non-set items. -/
def NonSet (x : A ⊕ C) : Prop := ∀ c, x = .inr c → H.isSet c = false

theorem exMI_nonset {x : A ⊕ C} (h : H.NonSet x) : H.exMI x = filt (H.exI x) := by
  cases x with
  | inl a => simp [exMI_inl, exI_inl, filt]
  | inr c => exact H.exMI_seq (h c rfl)

/-- **The expansion of a chain.** -/
def exC (xs : List (A ⊕ C)) : Multiset (List A) :=
  match xs with
  | [x] => H.exMI x
  | _ => filt (xs.flatMap H.exI)

theorem exC_nonset {xs : List (A ⊕ C)} (h : ∀ x ∈ xs, H.NonSet x) : H.exC xs = filt (xs.flatMap H.exI) := by
  match xs, h with
  | [x], h => simp only [exC, List.flatMap_cons, List.flatMap_nil, List.append_nil]
              exact H.exMI_nonset (h x (by simp))
  | [], _ => rfl
  | _ :: _ :: _, _ => rfl

theorem exC_single (x : A ⊕ C) : H.exC [x] = H.exMI x := rfl

theorem exC_nil : H.exC ([] : List (A ⊕ C)) = 0 := by simp [exC, filt]

/-- The number of decomposition steps an item needs. -/
def sz : A ⊕ C → ℕ
  | .inl _ => 0
  | .inr c => 1 + ((H.body c).attach.map fun x => sz x.1).sum
termination_by x => H.itemRk x
decreasing_by exact H.itemRk_lt x.2

theorem sz_inr (c : C) : H.sz (.inr c) = 1 + ((H.body c).map H.sz).sum := by
  rw [sz]
  conv_rhs => rw [← List.attach_map_subtype_val (H.body c)]
  rw [List.map_map]; rfl

end HSpec

/-! ## The invariant -/

variable {F A C : Type} (P : Problem F A C ℕ) (H : HSpec A C)

/-- The methods realise the bodies of the specification. -/
def Fit : Prop := ∀ m ∈ P.methods, m.subtasks.WF ∧
  (H.isSet m.abstractTask = true → ∃ l, SetNet m.subtasks l (H.body m.abstractTask)) ∧
  (H.isSet m.abstractTask = false → ∃ l, m.subtasks.IsSeqNet l (H.body m.abstractTask))

/-- Set-kind compound tasks only form pool chains of their own. -/
def Shape (cs : List (Ch ℕ A C)) : Prop :=
  ∀ j (hj : j < cs.length) c, Sum.inr c ∈ cs[j].2 → H.isSet c = true → j ≠ 0 ∧ cs[j].2 = [.inr c]

/-- The expansion of the pool chains. -/
def poolE (cs : List (Ch ℕ A C)) : Multiset (List A) := (cs.tail.map fun ch => H.exC ch.2).sum

/-- **The invariant**: a union of chains with the control expansion `ctlT` and the pool
expansion `poolT`. -/
def HInv (H : HSpec A C) (tn : TaskNetwork ℕ A C) (ctlT : List A) (poolT : Multiset (List A)) : Prop :=
  ∃ cs : List (Ch ℕ A C), ∃ h0 : 0 < cs.length, UC tn cs ∧ Shape H cs ∧
    cs[0].2.flatMap H.exI = ctlT ∧ poolE H cs = poolT

/-! ## Lists of chains -/

theorem sum_set {α M : Type} [AddCommMonoid M] (f : α → M) :
    ∀ (l : List α) (k : ℕ) (hk : k < l.length) (v : α),
      ((l.set k v).map f).sum + f l[k] = (l.map f).sum + f v := by
  intro l
  induction l with
  | nil => intro k hk; simp at hk
  | cons a l ih =>
    intro k hk v
    rcases k with _ | k
    · simp [add_comm, add_left_comm]
    · simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      rw [add_assoc, ih k (by simpa using hk) v, ← add_assoc]

theorem tail_set_succ {α : Type} (l : List α) (k : ℕ) (v : α) : (l.set (k + 1) v).tail = l.tail.set k v := by
  cases l <;> simp

variable {H}

/-- **Decomposition steps preserve the invariant.** -/
theorem HInv.step (hfit : Fit P H) {tn tn' : TaskNetwork ℕ A C} {t : ℕ} {m : Method ℕ A C}
    (hs : DecompStep P.methods tn t m tn') {ctlT : List A} {poolT : Multiset (List A)}
    (h : HInv H tn ctlT poolT) : HInv H tn' ctlT poolT := by
  obtain ⟨cs, h0, huc, hsh, hctl, hpool⟩ := h
  obtain ⟨hmM, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hs
  obtain ⟨hwf, hset, hseq⟩ := hfit m hmM
  set c := m.abstractTask with hc
  obtain ⟨k, hk, htk⟩ := (huc.mem t).1 htT
  have hlabk := huc.lab k hk
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem htk
  have hlabs : cs[k].2 = l₁.map tn.α ++ .inr c :: l₂.map tn.α := by
    rw [← hlabk, hsplit]; simp [hαt]
  have hck : cs[k] = (l₁ ++ t :: l₂, l₁.map tn.α ++ .inr c :: l₂.map tn.α) := by
    rw [← hsplit, ← hlabs]
  have hiso' := huiso.symm
  cases hS : H.isSet c
  · -- a sequence body
    obtain ⟨l, hl⟩ := hseq hS
    obtain ⟨lm, hlm⟩ := hl.iso hu hiso'
    have huc' := huc.step_seq hk hck (by simp) hlm hdisj
    -- no set items in chain `k`
    have hnsk : ∀ x ∈ cs[k].2, H.NonSet x := by
      intro x hx d rfl
      by_contra hd
      have hd' : H.isSet d = true := by simpa using hd
      obtain ⟨-, he⟩ := hsh k hk d hx hd'
      rw [hlabs] at he
      have : Sum.inr c ∈ [(Sum.inr d : A ⊕ C)] := by rw [← he]; simp
      simp at this; rw [this] at hS; rw [hS] at hd'; cases hd'
    have hbody : ∀ x ∈ H.body c, H.NonSet x := by
      intro x hx d rfl; exact H.seq_items c hS d hx
    have hnew : ∀ x ∈ l₁.map tn.α ++ H.body c ++ l₂.map tn.α, H.NonSet x := by
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hnsk x (by rw [hlabs]; simp [hx])
      · exact hbody x hx
      · exact hnsk x (by rw [hlabs]; simp [hx])
    have hfl : (l₁.map tn.α ++ H.body c ++ l₂.map tn.α).flatMap H.exI =
        cs[k].2.flatMap H.exI := by
      rw [hlabs]; simp [H.exI_inr, List.flatMap_append]
    refine ⟨_, by simpa using h0, huc', fun j hj d hd hdS => ?_, ?_, ?_⟩
    · simp only [List.getElem_set] at hd ⊢
      split_ifs at hd ⊢ with hjk
      · exact absurd hdS (by rw [hnew _ hd d rfl]; simp)
      · exact hsh j (by simpa using hj) d hd hdS
    · rw [← hctl]
      simp only [List.getElem_set]
      split_ifs with h0k
      · subst h0k; exact hfl
      · rfl
    · rw [← hpool, poolE, poolE]
      rcases k with _ | k
      · simp [List.set]
        cases cs <;> simp_all
      · rw [tail_set_succ]
        have hk' : k < cs.tail.length := by simp; omega
        have e := sum_set (fun ch : Ch ℕ A C => H.exC ch.2) cs.tail k hk'
          (l₁ ++ lm ++ l₂, l₁.map tn.α ++ H.body c ++ l₂.map tn.α)
        have e2 : H.exC (cs.tail[k]'hk').2 = H.exC (l₁.map tn.α ++ H.body c ++ l₂.map tn.α) := by
          have : cs.tail[k]'hk' = cs[k + 1] := by simp
          rw [this, H.exC_nonset hnsk, H.exC_nonset hnew, hfl]
        rw [e2] at e
        exact add_right_cancel e
  · -- a set body
    obtain ⟨l, hl⟩ := hset hS
    obtain ⟨lm, hlm⟩ := hl.iso hu hiso'
    obtain ⟨hk0, he⟩ := hsh k hk c (by rw [hlabs]; simp) hS
    have hl12 : l₁ = [] ∧ l₂ = [] := by
      rw [hlabs] at he
      cases l₁ with
      | nil => cases l₂ with
        | nil => exact ⟨rfl, rfl⟩
        | cons _ _ => simp at he
      | cons _ _ => simp at he
    obtain ⟨rfl, rfl⟩ := hl12
    have hck' : cs[k] = ([t], [.inr c]) := by simpa using hck
    have huc' := huc.step_set hk hck' hlm hdisj
    refine ⟨_, by simp; omega, huc', fun j hj d hd hdS => ?_, ?_, ?_⟩
    · have hn : (cs.set k ([], [])).length = cs.length := List.length_set ..
      rcases Nat.lt_or_ge j cs.length with hj' | hj'
      · rw [List.getElem_append_left (by rw [hn]; exact hj')] at hd ⊢
        simp only [List.getElem_set] at hd ⊢
        split_ifs at hd ⊢ with hjk
        · simp at hd
        · exact hsh j hj' d hd hdS
      · rw [List.getElem_append_right (by rw [hn]; exact hj')] at hd ⊢
        have hlm' : lm.length = (H.body c).length := by rw [← hlm.labels, List.length_map]
        rw [singles_get hlm'] at hd ⊢
        simp only [List.mem_singleton] at hd
        exact ⟨by omega, by rw [hd]⟩
    · rw [← hctl]
      have : 0 < (cs.set k ([], [])).length := by simp; omega
      rw [List.getElem_append_left this]
      simp [List.getElem_set, Ne.symm hk0, hk0]
    · rw [← hpool, poolE, poolE]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hne : 0 < (cs.set (k' + 1) ([], [])).length := by simp; omega
      rw [show (cs.set (k' + 1) ([], []) ++ singles lm (H.body c)).tail =
          (cs.set (k' + 1) ([], [])).tail ++ singles lm (H.body c) by
        cases hcs : cs.set (k' + 1) ([], []) with
        | nil => rw [hcs] at hne; simp at hne
        | cons _ _ => rfl]
      rw [tail_set_succ, List.map_append, List.sum_append]
      have hk' : k' < cs.tail.length := by simp; omega
      have e := sum_set (fun ch : Ch ℕ A C => H.exC ch.2) cs.tail k' hk' ([], [])
      have e2 : H.exC (cs.tail[k']'hk').2 = H.exMI (.inr c) := by
        have : cs.tail[k']'hk' = cs[k' + 1] := by simp
        rw [this, hck']; rfl
      rw [e2, H.exC_nil, add_zero, H.exMI_set hS] at e
      have hlm' : lm.length = (H.body c).length := by rw [← hlm.labels, List.length_map]
      have e3 : ((singles lm (H.body c)).map fun ch => H.exC ch.2).sum = ((H.body c).map H.exMI).sum := by
        congr 1
        refine List.ext_getElem (by simp [singles, hlm']) fun i h1 h2 => ?_
        rw [List.getElem_map, singles_get hlm', List.getElem_map]
        rfl
      rw [e3, ← e]

theorem HInv.decomposesTo (hfit : Fit P H) {tn tn' : TaskNetwork ℕ A C}
    (hd : DecomposesTo P.methods tn tn') {ctlT : List A} {poolT : Multiset (List A)}
    (h : HInv H tn ctlT poolT) : HInv H tn' ctlT poolT := by
  induction hd with
  | refl => exact h
  | tail _ hs ih => obtain ⟨t, m, hs⟩ := hs; exact HInv.step P hfit hs ih

/-! ## Primitive networks -/

theorem flatMap_single_map {α β : Type} (f : α → β) : ∀ l : List α, l.flatMap (fun a => [f a]) = l.map f
  | [] => rfl
  | a :: l => by simp [flatMap_single_map f l]

theorem mem_tail_map_fst {cs : List (Ch ℕ A C)} {c : List ℕ} :
    c ∈ cs.tail.map Prod.fst ↔ ∃ j, ∃ hj : j < cs.length, 0 < j ∧ cs[j].1 = c := by
  rw [List.mem_map]
  constructor
  · rintro ⟨ch, hch, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hch
    exact ⟨i + 1, by simp at hi; omega, by omega, by simp⟩
  · rintro ⟨j, hj, hj0, rfl⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨cs.tail[i]'(by simp; omega), List.getElem_mem _, by simp⟩

theorem filter_map_filt {β : Type} (g : List ℕ → List β) (hg : ∀ l, g l = [] ↔ l = []) :
    ∀ L : List (List ℕ), (((L.filter fun l => l ≠ []).map g : List (List β)) : Multiset (List β)) =
      (L.map fun l => HSpec.filt (g l)).sum := by
  intro L
  induction L with
  | nil => rfl
  | cons l L ih =>
    by_cases hl : l = []
    · subst hl
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, List.map_cons, List.sum_cons, ih]
      rw [HSpec.filt, if_pos ((hg []).2 rfl), zero_add]
    · simp only [List.filter_cons, ne_eq, hl, not_false_eq_true, decide_true, if_true,
        List.map_cons, List.sum_cons]
      rw [← Multiset.cons_coe, ih, HSpec.filt, if_neg (by rw [hg]; exact hl), Multiset.singleton_add]

/-- **On primitive networks the invariant is `IsChains`** with the expanded label lists. -/
theorem HInv.isChains [Inhabited A] {tn : TaskNetwork ℕ A C} (hprim : ∀ t ∈ tn.T, ∃ a, tn.α t = .inl a)
    {ctlT : List A} {poolT : Multiset (List A)} (h : HInv H tn ctlT poolT) :
    ∃ (ctl : List ℕ) (pool : Multiset (List ℕ)) (ℓ : ℕ → A), IsChains tn ctl pool ℓ ∧
      ctl.map ℓ = ctlT ∧ pool.map (List.map ℓ) = poolT := by
  classical
  obtain ⟨cs, h0, huc, -, hctl, hpool⟩ := h
  let ℓ : ℕ → A := fun t => match tn.α t with
    | .inl a => a
    | .inr _ => default
  have hℓ : ∀ t ∈ tn.T, tn.α t = .inl (ℓ t) := by
    intro t ht
    obtain ⟨a, ha⟩ := hprim t ht
    simp only [ℓ, ha]
  have hinT : ∀ j (hj : j < cs.length), ∀ x ∈ cs[j].1, x ∈ tn.T := fun j hj x hx =>
    (huc.mem x).2 ⟨j, hj, hx⟩
  have hlab : ∀ j (hj : j < cs.length), cs[j].2 = cs[j].1.map fun t => Sum.inl (ℓ t) := by
    intro j hj
    rw [← huc.lab j hj]
    exact List.map_congr_left fun x hx => hℓ x (hinT j hj x hx)
  let PL : List (List ℕ) := (cs.tail.map Prod.fst).filter fun l => l ≠ []
  have hPL : ∀ c, c ∈ PL ↔ c ≠ [] ∧ ∃ j, ∃ hj : j < cs.length, 0 < j ∧ cs[j].1 = c := by
    intro c
    simp only [PL, List.mem_filter, mem_tail_map_fst, ne_eq, decide_not, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not]
    tauto
  have hpw : (cs.tail.map Prod.fst).Pairwise fun a b => ∀ x ∈ a, x ∉ b := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij x hx
    simp only [List.getElem_map, List.getElem_tail] at hx ⊢
    simp at hi hj
    exact huc.disj (i + 1) (j + 1) (by omega) (by omega) (by omega) x hx
  have hPLnd : PL.Nodup := by
    have := (List.Pairwise.filter (fun l => decide (l ≠ [])) hpw)
    refine this.imp_of_mem fun {a b} ha hb hab e => ?_
    subst e
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil a ((hPL a).1 ha).1
    exact hab x hx hx
  refine ⟨cs[0].1, (PL : Multiset (List ℕ)), ℓ, ⟨fun x => ?_, fun x y => ?_, hℓ, huc.nodup 0 h0,
    fun c hc => ?_, fun c hc t ht => ?_, fun c hc t ht c' hc' => ?_⟩, ?_, ?_⟩
  · rw [huc.mem]
    constructor
    · rintro ⟨j, hj, hx⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact Or.inl hx
      · exact Or.inr ⟨cs[j].1, Multiset.mem_coe.2 ((hPL _).2 ⟨List.ne_nil_of_mem hx, j, hj, hj0, rfl⟩), hx⟩
    · rintro (hx | ⟨c, hc, hx⟩)
      · exact ⟨0, h0, hx⟩
      · obtain ⟨-, j, hj, -, rfl⟩ := (hPL c).1 (Multiset.mem_coe.1 hc)
        exact ⟨j, hj, hx⟩
  · rw [huc.ord]
    constructor
    · rintro ⟨j, hj, hb⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact Or.inl hb
      · exact Or.inr ⟨cs[j].1, Multiset.mem_coe.2 ((hPL _).2
          ⟨List.ne_nil_of_mem (before_mem hb).1, j, hj, hj0, rfl⟩), hb⟩
    · rintro (hb | ⟨c, hc, hb⟩)
      · exact ⟨0, h0, hb⟩
      · obtain ⟨-, j, hj, -, rfl⟩ := (hPL c).1 (Multiset.mem_coe.1 hc)
        exact ⟨j, hj, hb⟩
  · obtain ⟨-, j, hj, -, rfl⟩ := (hPL c).1 (Multiset.mem_coe.1 hc)
    exact huc.nodup j hj
  · obtain ⟨-, j, hj, hj0, rfl⟩ := (hPL c).1 (Multiset.mem_coe.1 hc)
    exact huc.disj j 0 hj h0 (by omega) t ht
  · rw [Multiset.Nodup.mem_erase_iff (Multiset.coe_nodup.2 hPLnd), Multiset.mem_coe] at hc'
    obtain ⟨hne, hc'⟩ := hc'
    obtain ⟨-, i, hi, -, rfl⟩ := (hPL c).1 (Multiset.mem_coe.1 hc)
    obtain ⟨-, j, hj, -, rfl⟩ := (hPL c').1 hc'
    have hij : i ≠ j := by rintro rfl; exact hne rfl
    exact huc.disj i j hi hj hij t ht
  · rw [← hctl, hlab 0 h0, List.flatMap_map]
    simp [HSpec.exI_inl, flatMap_single_map]
  · rw [← hpool, poolE, Multiset.map_coe, filter_map_filt (List.map ℓ) (fun l => List.map_eq_nil_iff),
      List.map_map]
    congr 1
    refine List.map_congr_left fun ch hch => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hch
    simp only [Function.comp_apply, List.getElem_tail]
    have hi' : i + 1 < cs.length := by simp at hi; omega
    rw [hlab (i + 1) hi', H.exC_nonset (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; intro d hd; cases hd)]
    simp [List.flatMap_map, HSpec.exI_inl, flatMap_single_map]

/-! ## Full decompositions exist -/

/-- The number of decomposition steps a network still needs. -/
noncomputable def mu (H : HSpec A C) (tn : TaskNetwork ℕ A C) : ℕ := ∑ x ∈ tn.T, H.sz (tn.α x)

theorem body_sz (hfit : Fit P H) {m : Method ℕ A C} (hm : m ∈ P.methods) :
    ∑ x ∈ m.subtasks.T, H.sz (m.subtasks.α x) = ((H.body m.abstractTask).map H.sz).sum := by
  obtain ⟨-, hset, hseq⟩ := hfit m hm
  have key : ∀ l : List ℕ, l.Nodup → (∀ x, x ∈ m.subtasks.T ↔ x ∈ l) →
      l.map m.subtasks.α = H.body m.abstractTask →
      ∑ x ∈ m.subtasks.T, H.sz (m.subtasks.α x) = ((H.body m.abstractTask).map H.sz).sum := by
    intro l hnd hmem hlab
    have hT : m.subtasks.T = l.toFinset := Finset.ext fun x => by rw [hmem, List.mem_toFinset]
    rw [hT, List.sum_toFinset _ hnd, ← hlab, List.map_map]; rfl
  cases hS : H.isSet m.abstractTask
  · obtain ⟨l, hl⟩ := hseq hS; exact key l hl.nodup hl.memT hl.labels
  · obtain ⟨l, hl⟩ := hset hS; exact key l hl.nodup hl.memT hl.labels

theorem mu_shift (m : TaskNetwork ℕ A C) (N : ℕ) :
    ∑ x ∈ (PCP.shiftNet m N).T, H.sz ((PCP.shiftNet m N).α x) = ∑ x ∈ m.T, H.sz (m.α x) := by
  simp only [PCP.shiftNet, Finset.sum_map, addRightEmbedding_apply, Nat.add_sub_cancel]

theorem mu_decompose {tn u : TaskNetwork ℕ A C} {t : ℕ} (ht : t ∈ tn.T) (hdisj : Disjoint tn.T u.T) :
    mu H (decomposeWith tn t u) + H.sz (tn.α t) = mu H tn + ∑ x ∈ u.T, H.sz (u.α x) := by
  have hd : Disjoint (tn.T.erase t) u.T := Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj
  simp only [mu, decomposeWith]
  rw [Finset.sum_union hd]
  have e1 : ∑ x ∈ tn.T.erase t, H.sz (if x ∈ u.T then u.α x else tn.α x) =
      ∑ x ∈ tn.T.erase t, H.sz (tn.α x) := Finset.sum_congr rfl fun x hx => by
    rw [if_neg fun h => Finset.disjoint_left.1 hd hx h]
  have e2 : ∑ x ∈ u.T, H.sz (if x ∈ u.T then u.α x else tn.α x) = ∑ x ∈ u.T, H.sz (u.α x) :=
    Finset.sum_congr rfl fun x hx => by rw [if_pos hx]
  rw [e1, e2, add_right_comm, Finset.sum_erase_add _ _ ht]

/-- **Every network can be decomposed fully** (if the compound names that occur have methods). -/
theorem exists_primitive (hfit : Fit P H) (R : C → Prop) (hRc : ∀ c d, R c → .inr d ∈ H.body c → R d)
    (hex : ∀ c, R c → ∃ m ∈ P.methods, m.abstractTask = c) :
    ∀ (n : ℕ) (tn : TaskNetwork ℕ A C), mu H tn = n → (∀ t ∈ tn.T, ∀ c, tn.α t = .inr c → R c) →
      ∃ tn', DecomposesTo P.methods tn tn' ∧ tn'.IsPrimitive := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro tn hn hR
  by_cases hprim : tn.IsPrimitive
  · exact ⟨tn, Relation.ReflTransGen.refl, hprim⟩
  · simp only [TaskNetwork.IsPrimitive, TaskNetwork.IsPrimitiveId, not_forall, not_exists] at hprim
    obtain ⟨t, ht, hna⟩ := hprim
    obtain ⟨c, hc⟩ : ∃ c, tn.α t = .inr c := by
      cases h : tn.α t with
      | inl a => exact absurd h (hna a)
      | inr c => exact ⟨c, rfl⟩
    obtain ⟨m, hm, hmc⟩ := hex c (hR t ht c hc)
    have hwf := (hfit m hm).1
    set N := tn.T.sup id + 1 with hN
    have hdisj : Disjoint tn.T (PCP.shiftNet m.subtasks N).T := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      have h1 := (PCP.mem_shiftNet.1 hx').1
      have h2 : x ≤ tn.T.sup id := Finset.le_sup (f := id) hx
      omega
    have hstep : DecompStep P.methods tn t m (decomposeWith tn t (PCP.shiftNet m.subtasks N)) :=
      ⟨hm, ht, by rw [hc, hmc], _, PCP.shiftNet_wf hwf N, PCP.shiftNet_iso _ N, hdisj, rfl⟩
    have hmu := mu_decompose (H := H) ht hdisj
    rw [mu_shift, body_sz P hfit hm, hc, HSpec.sz_inr, hmc] at hmu
    have hlt : mu H (decomposeWith tn t (PCP.shiftNet m.subtasks N)) < n := by omega
    have hR' : ∀ x ∈ (decomposeWith tn t (PCP.shiftNet m.subtasks N)).T, ∀ d,
        (decomposeWith tn t (PCP.shiftNet m.subtasks N)).α x = .inr d → R d := by
      intro x hx d hd
      simp only [decomposeWith] at hd
      split_ifs at hd with hxu
      · -- a new task: its label is in the body of `c`
        obtain ⟨-, hset, hseq⟩ := hfit m hm
        have hy := (PCP.mem_shiftNet.1 hxu).2
        have hmem : ∀ l : List ℕ, (∀ y, y ∈ m.subtasks.T ↔ y ∈ l) → l.map m.subtasks.α = H.body c →
            Sum.inr d ∈ H.body c := by
          intro l hmT hlab
          rw [← hlab]
          exact List.mem_map.2 ⟨_, (hmT _).1 hy, hd⟩
        refine hRc c d (hR t ht c hc) ?_
        cases hS : H.isSet c
        · obtain ⟨l, hl⟩ := hseq (by rw [hmc]; exact hS)
          exact hmem l hl.memT (by rw [hl.labels, hmc])
        · obtain ⟨l, hl⟩ := hset (by rw [hmc]; exact hS)
          exact hmem l hl.memT (by rw [hl.labels, hmc])
      · rcases (mem_decomposeWith_T.1 hx) with ⟨hx', -⟩ | hx'
        · exact hR x hx' d hd
        · exact absurd hx' hxu
    obtain ⟨tn', h1, h2⟩ := ih _ hlt _ rfl hR'
    exact ⟨tn', Relation.ReflTransGen.head ⟨t, m, hstep⟩ h1, h2⟩

/-! ## Execution of a head task -/

namespace UC

variable {A C : Type} {tn : TaskNetwork ℕ A C} {cs : List (Ch ℕ A C)}

theorem head_of_unconstrained (h : UC tn cs) {t : ℕ} (hu : tn.Unconstrained t) {k : ℕ}
    (hk : k < cs.length) (htk : t ∈ cs[k].1) : ∃ rest, cs[k].1 = t :: rest := by
  cases hck : cs[k].1 with
  | nil => rw [hck] at htk; simp at htk
  | cons a rest =>
    by_cases hat : a = t
    · exact ⟨rest, by rw [hat]⟩
    · exfalso
      rw [hck] at htk
      have htr : t ∈ rest := (List.mem_cons.1 htk).resolve_left (Ne.symm hat)
      refine hu.2 a ((h.mem a).2 ⟨k, hk, by rw [hck]; simp⟩) ((h.ord a t).2 ⟨k, hk, ?_⟩)
      rw [hck]; exact before_cons.2 (Or.inl ⟨rfl, htr⟩)

theorem progress (h : UC tn cs) {k : ℕ} (hk : k < cs.length) {t : ℕ} {rest : List ℕ} {y : A ⊕ C}
    {labs : List (A ⊕ C)} (hc : cs[k] = (t :: rest, y :: labs)) :
    UC (tn.progress t) (cs.set k (rest, labs)) := by
  have ht_only : ∀ j (hj : j < cs.length), t ∈ cs[j].1 → j = k :=
    h.chain_of_mem hk (by rw [hc]; simp)
  have hnd := h.nodup k hk
  rw [hc] at hnd
  have hlab := h.lab k hk
  rw [hc] at hlab
  simp only [List.map_cons, List.cons.injEq] at hlab
  refine ⟨fun x => ?_, fun a b => ?_, fun j hj => ?_, fun j hj => ?_, fun i j hi hj hij x hx => ?_⟩
  · rw [TaskNetwork.progress_T, Finset.mem_erase, h.mem]
    simp only [List.length_set, List.getElem_set]
    constructor
    · rintro ⟨hxt, j, hj, hx⟩
      refine ⟨j, hj, ?_⟩
      split_ifs with hjk
      · subst hjk; rw [hc] at hx; exact (List.mem_cons.1 hx).resolve_left hxt
      · exact hx
    · rintro ⟨j, hj, hx⟩
      split_ifs at hx with hjk
      · subst hjk
        exact ⟨fun e => (List.nodup_cons.1 hnd).1 (e ▸ hx), k, hk, by rw [hc]; simp [hx]⟩
      · exact ⟨fun e => hjk (ht_only j hj (e ▸ hx)).symm, j, hj, hx⟩
  · rw [TaskNetwork.progress_ord, h.ord]
    simp only [List.length_set, List.getElem_set]
    constructor
    · rintro ⟨⟨j, hj, hb⟩, hat⟩
      refine ⟨j, hj, ?_⟩
      split_ifs with hjk
      · subst hjk; rw [hc, before_cons] at hb
        rcases hb with ⟨rfl, -⟩ | hb
        · exact absurd rfl hat
        · exact hb
      · exact hb
    · rintro ⟨j, hj, hb⟩
      split_ifs at hb with hjk
      · subst hjk
        refine ⟨⟨k, hk, by rw [hc]; exact before_cons.2 (Or.inr hb)⟩, fun e => ?_⟩
        subst e; exact (List.nodup_cons.1 hnd).1 (before_mem hb).1
      · exact ⟨⟨j, hj, hb⟩, fun e => hjk (ht_only j hj (e ▸ (before_mem hb).1)).symm⟩
  · simp only [List.getElem_set, TaskNetwork.progress]
    split_ifs with hjk
    · exact hlab.2
    · exact h.lab j (by simpa using hj)
  · simp only [List.getElem_set]
    split_ifs with hjk
    · exact (List.nodup_cons.1 hnd).2
    · exact h.nodup j (by simpa using hj)
  · simp only [List.length_set] at hi hj
    simp only [List.getElem_set] at hx ⊢
    by_cases h1 : k = i
    · subst h1
      rw [if_pos rfl] at hx
      rw [if_neg hij]
      exact h.disj k j hk hj hij x (by rw [hc]; simp [hx])
    · rw [if_neg h1] at hx
      by_cases h2 : k = j
      · subst h2
        rw [if_pos rfl]
        intro hx'
        exact h.disj i k hi hk hij x hx (by rw [hc]; simp [hx'])
      · rw [if_neg h2]; exact h.disj i j hi hj hij x hx

end UC

end AcycHard

end FOND
