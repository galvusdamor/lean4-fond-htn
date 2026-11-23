import FondHtn.FairUndec.Sound
import FondHtn.FairUndec.ChainFair
/-!
# Infinite runs give fair solutions

**`FOND.FU.fair_of_inf`**: if the two-stack machine has an infinite run from the initial
configuration, the description has a fair strong cyclic solution.

The fair chain game (`FOND.FU.fairWin_of_chains`) is played on three chains: an empty one and the
two stacks (`FOND.FU.posA`).  Along the run, the policy decomposes the top symbol of the stack of
the run's next transition and executes the transition (`FOND.FU.posB`).  Its tick outcome leads
to a *drain* position (`FOND.FU.Drn`), from which everything is drained; the cost of the chains
decreases with every drain move.  So the stop outcome of the next transition is always a way to
the goal.
-/

namespace FOND

namespace FU

open HTN HTN.Syn HTN.Article HTN.Undec AcycHard.Sav HardTR HardMP

variable {M : TSM} {s₁ s₂ : List ℕ} {tk : ℕ → Bool}

/-! ## Positions -/

/-- The labels of a stack. -/
def stackLab (b : Bool) (s : List ℕ) : List (ℕ ⊕ ℕ) := s.map (fun a => Sum.inr (sym b a)) ++ [Sum.inr (bot b)]

/-- The steady positions: the two stacks. -/
def posA (c : Undec.Cfg) : List (LCh ℕ ℕ) :=
  [⟨[], none⟩, ⟨stackLab false c.s1, none⟩, ⟨stackLab true c.s2, none⟩]

/-- The chain of a stack. -/
def kOf (b : Bool) : ℕ := if b then 2 else 1

/-- After decomposing the top of the stack with the transition `n`. -/
def posB (M : TSM) (c : Undec.Cfg) (n : ℕ) (rest : List ℕ) : List (LCh ℕ ℕ) :=
  (posA c).set (kOf (tr M n).stk) ⟨Sum.inl (aT n) :: stackLab (tr M n).stk ((tr M n).push ++ rest), none⟩

/-- The initial positions. -/
def pos0 : List (LCh ℕ ℕ) := [⟨[Sum.inr root0], none⟩]
def pos1 : List (LCh ℕ ℕ) := [⟨[], none⟩, ⟨[Sum.inr (root false)], none⟩, ⟨[Sum.inr (root true)], none⟩]
def pos2 (s₁ : List ℕ) : List (LCh ℕ ℕ) :=
  [⟨[], none⟩, ⟨stackLab false s₁, none⟩, ⟨[Sum.inr (root true)], none⟩]

/-- Drainable labels. -/
def DL (M : TSM) (s₁ s₂ : List ℕ) (x : ℕ ⊕ ℕ) : Prop :=
  (∃ b a, a ∈ alph M s₁ s₂ ∧ x = .inr (sym b a)) ∨ (∃ b, x = .inr (bot b)) ∨ x = .inl aD

/-- **Drain positions**: stopped, every label drainable. -/
def Drn (M : TSM) (s₁ s₂ : List ℕ) (ls : List (LCh ℕ ℕ)) (s : Set ℕ) : Prop :=
  fStop ∈ s ∧ ∀ c ∈ ls, c.tag = none ∧ ∀ x ∈ c.lab, DL M s₁ s₂ x

/-- A step of the run through the transition `n`, the stack being `pop :: rest`. -/
def RunStep (M : TSM) (f : ℕ → Undec.Cfg) (i n : ℕ) (rest : List ℕ) : Prop :=
  n < M.trans.length ∧ (f i).st = (tr M n).src ∧ stkC (f i) (tr M n).stk = (tr M n).pop :: rest ∧
    f (i + 1) = nxt M (f i) n rest

/-- **The fair set of positions** along the run `f`. -/
def Zf (M : TSM) (s₁ s₂ : List ℕ) (f : ℕ → Undec.Cfg) (ls : List (LCh ℕ ℕ)) (s : Set ℕ) : Prop :=
  (∃ i, ls = posA (f i) ∧ s = {fq (f i).st}) ∨
  (∃ i n rest, RunStep M f i n rest ∧ ls = posB M (f i) n rest ∧ s = {fq (f i).st}) ∨
  (s = {fq M.start} ∧ (ls = pos0 ∨ ls = pos1 ∨ ls = pos2 s₁)) ∨ Drn M s₁ s₂ ls s

/-! ## Methods -/

theorem mem_meth {e : MethodDesc} (he : e ∈ meths M s₁ s₂) :
    e.toMethod ∈ (desc M s₁ s₂ tk).toProblem.methods := ⟨e, he, rfl⟩

theorem mem_methT {n : ℕ} (hn : n < M.trans.length) : methT M n ∈ meths M s₁ s₂ := by
  simp only [meths, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩))))

theorem mem_drainM {b : Bool} {a : ℕ} (ha : a ∈ alph M s₁ s₂) :
    (sym b a, seqTn [(false, aD)]) ∈ meths M s₁ s₂ := by
  simp only [meths, List.mem_append]
  refine Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨b, by cases b <;> simp, List.mem_map.2 ⟨a, ha, rfl⟩⟩))))

theorem mem_botM (b : Bool) : (bot b, seqTn [(false, aD)]) ∈ meths M s₁ s₂ := by
  simp only [meths, List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨b, by cases b <;> simp, rfl⟩)))

theorem mem_rootM (b : Bool) :
    (root b, seqTn (symL b (stk0 s₁ s₂ b) ++ [(true, bot b)])) ∈ meths M s₁ s₂ := by
  simp only [meths, List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.2 ⟨b, by cases b <;> simp, rfl⟩))

theorem mem_root0M : (root0, setTn [(true, root false), (true, root true)]) ∈ meths M s₁ s₂ := by
  simp [meths]

theorem labs_seq (ls : List (Bool × ℕ)) : ∃ l, (seqTn ls).toTaskNetwork.IsSeqNet l (ls.map toLab) :=
  ⟨_, isSeqNet_seqTn ls⟩

theorem map_symL (b : Bool) (s : List ℕ) :
    (symL b s).map toLab = s.map fun a => Sum.inr (sym b a) := by
  simp [symL, toLab]

/-! ## Costs -/

/-- The cost of draining a label. -/
def costX : ℕ ⊕ ℕ → ℕ
  | .inl _ => 1
  | .inr _ => 2

/-- The cost of draining the chains. -/
def cost (ls : List (LCh ℕ ℕ)) : ℕ := (ls.map fun c => (c.lab.map costX).sum).sum

theorem sum_set_lt : ∀ {l : List ℕ} {k : ℕ} (hk : k < l.length) {x : ℕ}, x < l[k] → (l.set k x).sum < l.sum
  | [], _, hk, _, _ => by simp at hk
  | y :: l, 0, _, x, hx => by simp at hx ⊢; omega
  | y :: l, k + 1, hk, x, hx => by
    simp only [List.set_cons_succ, List.sum_cons]
    have := sum_set_lt (l := l) (k := k) (by simpa using hk) (x := x) (by simpa using hx)
    omega

theorem cost_set_lt {ls : List (LCh ℕ ℕ)} {k : ℕ} (hk : k < ls.length) {c : LCh ℕ ℕ}
    (h : (c.lab.map costX).sum < (ls[k].lab.map costX).sum) : cost (ls.set k c) < cost ls := by
  unfold cost
  rw [List.map_set]
  exact sum_set_lt (by simpa using hk) (by simpa using h)

/-! ## Draining -/

variable (M s₁ s₂) in
theorem ca_drn (f : ℕ → Undec.Cfg) :
    ∀ N ls s, cost ls ≤ N → Drn M s₁ s₂ ls s → ∃ n, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) n ls s := by
  intro N
  induction N with
  | zero =>
    intro ls s hc _
    refine ⟨0, .goal fun c hcm => ?_⟩
    have : (c.lab.map costX).sum = 0 := by
      have := List.le_sum_of_mem (List.mem_map.2 ⟨c, hcm, rfl⟩ :
        (c.lab.map costX).sum ∈ ls.map fun c => (c.lab.map costX).sum)
      unfold cost at hc; omega
    rcases hl : c.lab with _ | ⟨x, l⟩
    · rfl
    · rw [hl] at this; cases x <;> simp [costX] at this
  | succ N ih =>
    intro ls s hc hd
    by_cases hall : ∀ c ∈ ls, c.lab = []
    · exact ⟨0, .goal hall⟩
    push_neg at hall
    obtain ⟨c, hcm, hne⟩ := hall
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcm
    obtain ⟨htag, hdl⟩ := hd.2 _ hcm
    obtain ⟨x, rest, hlab⟩ := List.exists_cons_of_ne_nil hne
    have hc' : ls[k] = ⟨x :: rest, none⟩ := by rw [← hlab, ← htag]
    have hdx := hdl x (by rw [hlab]; simp)
    have hdrest : ∀ y ∈ rest, DL M s₁ s₂ y := fun y hy => hdl y (by rw [hlab]; simp [hy])
    have hdset : ∀ l, (∀ y ∈ l, DL M s₁ s₂ y) → Drn M s₁ s₂ (ls.set k ⟨l, none⟩) s := by
      intro l hl
      refine ⟨hd.1, fun c' hc'm => ?_⟩
      rcases List.mem_or_eq_of_mem_set hc'm with h | rfl
      · exact hd.2 c' h
      · exact ⟨rfl, hl⟩
    rcases hdx with ⟨b, a, ha, rfl⟩ | ⟨b, rfl⟩ | rfl
    · -- a symbol: decompose by the drain method
      have hlt := cost_set_lt hk (c := ⟨[] ++ [Sum.inl aD] ++ rest, none⟩) (by rw [hlab]; simp [costX])
      obtain ⟨n, hn⟩ := ih (ls.set k ⟨[] ++ [Sum.inl aD] ++ rest, none⟩) s (by omega) (hdset _ (by
        intro y hy; simp only [List.nil_append, List.singleton_append, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Or.inr (Or.inr rfl)
        · exact hdrest y hy))
      refine ⟨n + 1, .seq hk (xs₁ := []) (by simpa using hc') (mem_meth (mem_drainM ha)) rfl
        (labs_seq _) (Or.inr (Or.inr (Or.inr (hdset _ ?_)))) (by simpa using hn)⟩
      intro y hy; simp only [List.nil_append, List.map_cons, List.map_nil, toLab, Bool.false_eq_true,
        ↓reduceIte, List.cons_append, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Or.inr (Or.inr rfl)
      · exact hdrest y hy
    · -- a bottom
      have hlt := cost_set_lt hk (c := ⟨[] ++ [Sum.inl aD] ++ rest, none⟩) (by rw [hlab]; simp [costX])
      obtain ⟨n, hn⟩ := ih (ls.set k ⟨[] ++ [Sum.inl aD] ++ rest, none⟩) s (by omega) (hdset _ (by
        intro y hy; simp only [List.nil_append, List.singleton_append, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Or.inr (Or.inr rfl)
        · exact hdrest y hy))
      refine ⟨n + 1, .seq hk (xs₁ := []) (by simpa using hc') (mem_meth (mem_botM b)) rfl
        (labs_seq _) (Or.inr (Or.inr (Or.inr (hdset _ ?_)))) (by simpa using hn)⟩
      intro y hy; simp only [List.nil_append, List.map_cons, List.map_nil, toLab, Bool.false_eq_true,
        ↓reduceIte, List.cons_append, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Or.inr (Or.inr rfl)
      · exact hdrest y hy
    · -- a drain action
      have hlt := cost_set_lt hk (c := ⟨rest, none⟩) (by rw [hlab]; simp [costX])
      obtain ⟨n, hn⟩ := ih (ls.set k ⟨rest, none⟩) s (by omega) (hdset _ hdrest)
      have happ : ((desc M s₁ s₂ tk).toProblem.δ aD).Applicable s := by
        rw [δ_aD, app_aD]; exact hd.1
      have hout : ((desc M s₁ s₂ tk).toProblem.δ aD).outcomes s = {s} := by rw [δ_aD, outcomes_aD]
      refine ⟨n + 1, .prim hk hc' (fun g h => by simp at h) happ (fun s' hs' => ?_) (by rw [hout]; rfl) hn⟩
      rw [hout, Set.mem_singleton_iff] at hs'
      subst hs'
      exact Or.inr (Or.inr (Or.inr (hdset _ hdrest)))

/-! ## The run -/

/-- The symbols on the stacks of a configuration are symbols of the machine. -/
def AlphOK (M : TSM) (s₁ s₂ : List ℕ) (c : Undec.Cfg) : Prop :=
  ∀ a, a ∈ c.s1 ∨ a ∈ c.s2 → a ∈ alph M s₁ s₂

theorem push_mem_alph {n : ℕ} (hn : n < M.trans.length) {a : ℕ} (ha : a ∈ (tr M n).push) :
    a ∈ alph M s₁ s₂ := by
  simp only [alph, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact Or.inr ⟨tr M n, tr_mem hn, Or.inr ha⟩

theorem alphOK_nxt {c : Undec.Cfg} (hc : AlphOK M s₁ s₂ c) {n : ℕ} (hn : n < M.trans.length)
    {rest : List ℕ} (h : stkC c (tr M n).stk = (tr M n).pop :: rest) :
    AlphOK M s₁ s₂ (nxt M c n rest) := by
  intro a ha
  unfold nxt at ha
  cases hb : (tr M n).stk <;> rw [hb] at h ha <;> simp [stkC] at h ha
  · rcases ha with (ha | ha) | ha
    · exact push_mem_alph hn ha
    · exact hc a (Or.inl (by rw [h]; simp [ha]))
    · exact hc a (Or.inr ha)
  · rcases ha with ha | ha | ha
    · exact hc a (Or.inl ha)
    · exact push_mem_alph hn ha
    · exact hc a (Or.inr (by rw [h]; simp [ha]))

theorem runStep_of_step {f : ℕ → Undec.Cfg} {i : ℕ} (h : M.Step (f i) (f (i + 1))) :
    ∃ n rest, RunStep M f i n rest := by
  obtain ⟨t, ht, hsrc, hcase⟩ := h
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 ht
  have htr : tr M n = M.trans[n] := by rw [tr, List.getD_eq_getElem _ _ hn]
  rw [← htr] at hsrc hcase
  rcases hcase with ⟨hb, rest, h1, h2⟩ | ⟨hb, rest, h1, h2⟩
  · exact ⟨n, rest, hn, hsrc, by simp [stkC, hb, h1], by rw [h2]; simp [nxt, hb]⟩
  · exact ⟨n, rest, hn, hsrc, by simp [stkC, hb, h1], by rw [h2]; simp [nxt, hb]⟩

theorem drn_posA {c : Undec.Cfg} (hc : AlphOK M s₁ s₂ c) {s : Set ℕ} (hs : fStop ∈ s) :
    Drn M s₁ s₂ (posA c) s := by
  refine ⟨hs, fun ch hch => ?_⟩
  simp only [posA, List.mem_cons, List.not_mem_nil, or_false] at hch
  rcases hch with rfl | rfl | rfl
  · exact ⟨rfl, by simp⟩
  · refine ⟨rfl, fun x hx => ?_⟩
    simp only [stackLab, List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨a, ha, rfl⟩ | rfl
    · exact Or.inl ⟨false, a, hc a (Or.inl ha), rfl⟩
    · exact Or.inr (Or.inl ⟨false, rfl⟩)
  · refine ⟨rfl, fun x hx => ?_⟩
    simp only [stackLab, List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨a, ha, rfl⟩ | rfl
    · exact Or.inl ⟨true, a, hc a (Or.inr ha), rfl⟩
    · exact Or.inr (Or.inl ⟨true, rfl⟩)

theorem stackLab_cons (b : Bool) (a : ℕ) (s : List ℕ) :
    stackLab b (a :: s) = Sum.inr (sym b a) :: stackLab b s := rfl

theorem bs_methT (n : ℕ) (rest : List ℕ) :
    [] ++ ((false, aT n) :: symL (tr M n).stk (tr M n).push).map toLab ++ stackLab (tr M n).stk rest =
      Sum.inl (aT n) :: stackLab (tr M n).stk ((tr M n).push ++ rest) := by
  simp [symL, toLab, stackLab]

variable (M s₁ s₂) in
/-- **The fair set of the run.** -/
theorem cset_run {f : ℕ → Undec.Cfg} (hf0 : f 0 = ⟨M.start, s₁, s₂⟩)
    (hf : ∀ i, M.Step (f i) (f (i + 1))) (hrec : ∀ i, ∃ j, i ≤ j ∧ tk (f (j + 1)).st = true) :
    CSet (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) := by
  -- the stacks hold symbols of the machine
  have halph : ∀ i, AlphOK M s₁ s₂ (f i) := by
    intro i
    induction i with
    | zero =>
      rw [hf0]; intro a ha
      simp only [alph, List.mem_append]
      rcases ha with ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr ha)
    | succ i ih =>
      obtain ⟨n, rest, hn, -, hst, he⟩ := runStep_of_step (hf i)
      rw [he]; exact alphOK_nxt ih hn hst
  have hdrn := ca_drn (tk := tk) M s₁ s₂ f
  -- after the transition: one outcome (the tick, if any, or the continuation) leads to a
  -- position of the attractor
  have hB : ∀ i n rest, RunStep M f i n rest →
      ((tk (f (i + 1)).st = true) ∨
        ∃ m, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) m (posA (f (i + 1))) {fq (f (i + 1)).st}) →
      ∃ m, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) m (posB M (f i) n rest) {fq (f i).st} := by
    rintro i n rest ⟨hn, hsrc, hst, he⟩ hnext
    have hd := drn_posA (halph (i + 1)) (s := {fq (f i).st} ∪ {fStop}) (by simp)
    have happ : ((desc M s₁ s₂ tk).toProblem.δ (aT n)).Applicable {fq (f i).st} := by
      rw [δ_aT M s₁ s₂ tk hn, app_aT]
      exact ⟨by simp [hsrc], by simpa using (fq_ne_stop _).symm⟩
    have hst' : (f (i + 1)).st = (tr M n).tgt := by rw [he]; unfold nxt; split_ifs <;> rfl
    have hcont : ({fq (f i).st} \ {fq (tr M n).src}) ∪ {fq (tr M n).tgt} = ({fq (f (i + 1)).st} : Set ℕ) := by
      rw [hst', hsrc]; ext x; simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]; tauto
    have hout : ((desc M s₁ s₂ tk).toProblem.δ (aT n)).outcomes {fq (f i).st} =
        insert {fq (f (i + 1)).st}
          {s' | tk (f (i + 1)).st = true ∧ s' = {fq (f i).st} ∪ {fStop}} := by
      rw [δ_aT M s₁ s₂ tk hn, outcomes_aT, hcont, hst']
    have hset : (posB M (f i) n rest).set (kOf (tr M n).stk)
        ⟨stackLab (tr M n).stk ((tr M n).push ++ rest), none⟩ = posA (f (i + 1)) := by
      rw [he]
      simp only [posB, posA, kOf, nxt]
      cases hb : (tr M n).stk <;> simp [hb]
    have hk : kOf (tr M n).stk < (posB M (f i) n rest).length := by
      simp only [posB, posA, kOf]; split_ifs <;> simp
    have hc : (posB M (f i) n rest)[kOf (tr M n).stk] =
        ⟨Sum.inl (aT n) :: stackLab (tr M n).stk ((tr M n).push ++ rest), none⟩ := by
      simp only [posB, posA, kOf]; split_ifs <;> simp
    have hall : ∀ s' ∈ ((desc M s₁ s₂ tk).toProblem.δ (aT n)).outcomes {fq (f i).st},
        Zf M s₁ s₂ f ((posB M (f i) n rest).set (kOf (tr M n).stk)
          ⟨stackLab (tr M n).stk ((tr M n).push ++ rest), none⟩) s' := by
      intro s' hs'
      rw [hout] at hs'
      rw [hset]
      rcases hs' with rfl | ⟨-, rfl⟩
      · exact Or.inl ⟨i + 1, rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr hd))
    rcases hnext with htk | ⟨m, hm⟩
    · obtain ⟨m, hm⟩ := hdrn _ _ _ le_rfl hd
      exact ⟨m + 1, .prim hk hc (fun g h => by simp at h) happ hall
        (s₀ := {fq (f i).st} ∪ {fStop}) (by rw [hout]; exact Or.inr ⟨htk, rfl⟩)
        (by rw [hset]; exact hm)⟩
    · exact ⟨m + 1, .prim hk hc (fun g h => by simp at h) happ hall
        (s₀ := {fq (f (i + 1)).st}) (by rw [hout]; exact Or.inl rfl) (by rw [hset]; exact hm)⟩
  -- the steady positions
  have hA' : ∀ i, ((tk (f (i + 1)).st = true) ∨
        ∃ m, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) m (posA (f (i + 1))) {fq (f (i + 1)).st}) →
      ∃ m, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) m (posA (f i)) {fq (f i).st} := by
    intro i hnext
    obtain ⟨n, rest, hrs⟩ := runStep_of_step (hf i)
    obtain ⟨m, hm⟩ := hB i n rest hrs hnext
    have hrs' := hrs
    obtain ⟨hn, -, hst, -⟩ := hrs'
    have hk : kOf (tr M n).stk < (posA (f i)).length := by simp only [posA, kOf]; split_ifs <;> simp
    have hc : (posA (f i))[kOf (tr M n).stk] =
        ⟨[] ++ Sum.inr (sym (tr M n).stk (tr M n).pop) :: stackLab (tr M n).stk rest, none⟩ := by
      simp only [stkC] at hst
      simp only [posA, kOf]
      split_ifs with hb <;> simp only [hb, if_true, Bool.false_eq_true, if_false] at hst <;>
        simp [hst, stackLab_cons, hb]
    have hset : (posA (f i)).set (kOf (tr M n).stk)
        ⟨[] ++ ((false, aT n) :: symL (tr M n).stk (tr M n).push).map toLab ++
          stackLab (tr M n).stk rest, none⟩ = posB M (f i) n rest := by
      rw [bs_methT]; rfl
    refine ⟨m + 1, .seq hk hc (mem_meth (mem_methT hn)) rfl (labs_seq _) ?_ (by rw [hset]; exact hm)⟩
    rw [hset]
    exact Or.inr (Or.inl ⟨i, n, rest, hrs, rfl, rfl⟩)
  -- by induction on the distance to the next tick
  have hAd : ∀ d i, tk (f (i + d + 1)).st = true →
      ∃ m, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) m (posA (f i)) {fq (f i).st} := by
    intro d
    induction d with
    | zero => intro i h; exact hA' i (Or.inl h)
    | succ d ih =>
      intro i h
      exact hA' i (Or.inr (ih (i + 1) (by rw [show i + 1 + d + 1 = i + (d + 1) + 1 by omega]; exact h)))
  have hA : ∀ i, ∃ m, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) m (posA (f i)) {fq (f i).st} := by
    intro i
    obtain ⟨j, hij, hj⟩ := hrec i
    exact hAd (j - i) i (by rw [show i + (j - i) + 1 = j + 1 by omega]; exact hj)
  -- the initial positions
  have h2 : ∃ m, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) m (pos2 s₁) {fq M.start} := by
    obtain ⟨m, hm⟩ := hA 0
    rw [hf0] at hm
    have hset : (pos2 s₁).set 2 ⟨[] ++ (symL true (stk0 s₁ s₂ true) ++ [(true, bot true)]).map toLab ++ [],
        none⟩ = posA ⟨M.start, s₁, s₂⟩ := by
      simp [pos2, posA, stk0, symL, toLab, stackLab]
    refine ⟨m + 1, .seq (k := 2) (by simp [pos2]) (xs₁ := []) (xs₂ := []) (c := root true) (τ := none) (by simp [pos2])
      (mem_meth (mem_rootM true)) rfl (labs_seq _) ?_ (by rw [hset]; exact hm)⟩
    rw [hset]
    exact Or.inl ⟨0, by rw [hf0], by rw [hf0]⟩
  have h1 : ∃ m, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) m pos1 {fq M.start} := by
    obtain ⟨m, hm⟩ := h2
    have hset : pos1.set 1 ⟨[] ++ (symL false (stk0 s₁ s₂ false) ++ [(true, bot false)]).map toLab ++ [],
        none⟩ = pos2 s₁ := by
      simp [pos1, pos2, stk0, symL, toLab, stackLab]
    refine ⟨m + 1, .seq (k := 1) (by simp [pos1]) (xs₁ := []) (xs₂ := []) (c := root false) (τ := none) (by simp [pos1])
      (mem_meth (mem_rootM false)) rfl (labs_seq _) ?_ (by rw [hset]; exact hm)⟩
    rw [hset]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩))
  have h0 : ∃ m, CA (desc M s₁ s₂ tk).toProblem (Zf M s₁ s₂ f) m pos0 {fq M.start} := by
    obtain ⟨m, hm⟩ := h1
    have hset : pos0.set 0 ⟨[], none⟩ ++ ([(true, root false), (true, root true)].map toLab).map
        (fun b => (⟨[b], none⟩ : LCh ℕ ℕ)) = pos1 := by
      simp [pos0, pos1, toLab]
    refine ⟨m + 1, .set (k := 0) (by simp [pos0]) (c := root0) (τ := none) (by simp [pos0])
      (mem_meth mem_root0M) rfl ⟨_, setNet_setTn _⟩ ?_ (by rw [hset]; exact hm)⟩
    rw [hset]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩))
  intro ls s hz
  rcases hz with ⟨i, rfl, rfl⟩ | ⟨i, n, rest, hrs, rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | hd
  · exact hA i
  · exact hB i n rest hrs (Or.inr (hA (i + 1)))
  · exact h0
  · exact h1
  · exact h2
  · exact hdrn _ _ _ le_rfl hd

/-- **Recurrent runs give fair solutions.** -/
theorem fair_of_rec (h : Rec tk M ⟨M.start, s₁, s₂⟩) :
    (desc M s₁ s₂ tk).toProblem.MPStrongCyclicFairSolvable := by
  obtain ⟨f, hf0, hf, hrec⟩ := h
  refine Problem.fair_of_fairWin ?_
  have htn : (desc M s₁ s₂ tk).toProblem.tnI = (seqTn [(true, root0)]).toTaskNetwork := rfl
  have hinit : (desc M s₁ s₂ tk).toProblem.init = {fq M.start} := by
    ext x; simp [desc, FProbDesc.toProblem, FProbDesc.init]
  rw [htn, hinit]
  refine fairWin_of_chains (cset_run M s₁ s₂ hf0 hf hrec) (TnDesc.toTaskNetwork_wf _)
    (TC.of_isSeqNet (isSeqNet_seqTn [(true, root0)])) ?_
  exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl (by simp [pos0, TCh.proj, toLab])⟩))

/-- **Infinite runs give fair solutions** (every transition ticks). -/
theorem fair_of_inf (h : Inf M ⟨M.start, s₁, s₂⟩) :
    (desc M s₁ s₂ fun _ => true).toProblem.MPStrongCyclicFairSolvable :=
  fair_of_rec (rec_true_iff.2 h)

/-- **Fair solvability of the description is an infinite run** (every transition ticks). -/
theorem fair_iff_inf :
    (desc M s₁ s₂ fun _ => true).toProblem.MPStrongCyclicFairSolvable ↔ Inf M ⟨M.start, s₁, s₂⟩ :=
  ⟨inf_of_fair, fair_of_inf⟩

end FU

end FOND
