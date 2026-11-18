import HtnComplexity.Complexity.RecMemUniform
/-!
# A description of quadratic size whose plans are exponentially long

`HtnComplexity/Complexity/AltBlowup.lean` exhibits, for the *counted* encoding, a domain
description of linear size all of whose plans have `2 ^ n - 1` actions.  There the exponential
length comes from universal branching in an **acyclic** hierarchy: the description already names
the `n` levels of the computation, so the plans are long but the recursion is bounded, and a
class of bounded recursion depth reproduces the description.

This file does the same for the **recursive** encoding of
`HtnComplexity/Complexity/RecMemDom.lean`, and the mechanism is the one §30.3 of `NOTES.md`
asks for: the description does not name the steps at all.  The machine
`HTN.Syn.counterMach n` is an `n`-bit **binary counter** — in the state `i` it clears the bit `i`
and carries on to `i + 1` if that bit is set, and otherwise sets it and starts the next increment
— and it accepts when the counter is full.  So

* `HTN.Syn.size_rmDom_counterMach_le` — the description has size at most `16 n ^ 2 + 72 n + 44`;
* `HTN.Syn.solvable_rmDom_counterMach` — the encoded problem is solvable, for every word;
* `HTN.Syn.length_ge_of_plan_counterMach` — and **every** plan has at least `2 ^ n` actions.

The recursion is what carries the length: the plan is a chain of `2 ^ n` nested refinements of a
single configuration task, not a tree of depth `n` over `n` distinct ones.
-/

namespace HTN

namespace Syn

/-! ### The value of the counter -/

/-- The number the first `n` memory bits encode, least significant bit first. -/
def ctrVal (n : ℕ) (μ : ℕ → Bool) : ℕ :=
  ((List.range n).map fun j => if μ j then 2 ^ j else 0).sum

@[simp] theorem ctrVal_zero (μ : ℕ → Bool) : ctrVal 0 μ = 0 := by simp [ctrVal]

theorem ctrVal_succ (n : ℕ) (μ : ℕ → Bool) :
    ctrVal (n + 1) μ = ctrVal n μ + (if μ n then 2 ^ n else 0) := by
  simp [ctrVal, List.range_succ]

theorem ctrVal_lt (n : ℕ) (μ : ℕ → Bool) : ctrVal n μ < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ctrVal_succ, pow_succ]
    cases hmu : μ n with
    | false => norm_num; omega
    | true => norm_num; omega

theorem ctrVal_memUpd (n : ℕ) (μ : ℕ → Bool) (i : ℕ) (v : Bool) (hi : i < n) :
    ctrVal n (memUpd μ i v) + (if μ i then 2 ^ i else 0)
      = ctrVal n μ + (if v then 2 ^ i else 0) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [ctrVal_succ, ctrVal_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
    · have hne : n ≠ i := by omega
      rw [memUpd_of_ne hne]
      have := ih hlt
      omega
    · subst heq
      have hsame : ctrVal i (memUpd μ i v) = ctrVal i μ := by
        simp only [ctrVal]
        refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        rw [memUpd_of_ne (by simp only [List.mem_range] at hj; omega)]
      rw [hsame, memUpd_self]
      omega

theorem ctrVal_set (n : ℕ) (μ : ℕ → Bool) (i : ℕ) (hi : i < n) (h : μ i = false) :
    ctrVal n (memUpd μ i true) = ctrVal n μ + 2 ^ i := by
  have := ctrVal_memUpd n μ i true hi
  rw [h] at this
  simpa using this

theorem ctrVal_clear (n : ℕ) (μ : ℕ → Bool) (i : ℕ) (hi : i < n) (h : μ i = true) :
    ctrVal n (memUpd μ i false) + 2 ^ i = ctrVal n μ := by
  have := ctrVal_memUpd n μ i false hi
  rw [h] at this
  simpa using this

theorem ctrVal_of_all_true {n : ℕ} {μ : ℕ → Bool} (h : ∀ j < n, μ j = true) :
    ctrVal n μ + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih fun j hj => h j (by omega)
    rw [ctrVal_succ, h n (by omega), pow_succ]
    norm_num
    omega

theorem ctrVal_of_all_false {n : ℕ} {μ : ℕ → Bool} (h : ∀ j, μ j = false) : ctrVal n μ = 0 := by
  simp [ctrVal, h]

/-! ### The counter machine -/

/-- **The `n`-bit binary counter**, as a recursive alternating machine with a memory.  In the
state `i` it either sets the bit `i`, which is the end of an increment, and returns to the state
`0`; or, if that bit is already set, clears it and carries to the state `i + 1`.  It accepts in
the state `0` with every bit set. -/
def counterMach (n : ℕ) : RecAltMem where
  mem := n
  start := 0
  acc := [(0, [], (List.range n).map fun j => (j, true))]
  ex := (List.range n).flatMap fun i =>
    [((i, [], [], (i, false, true), 0) : RmExTr), ((i, [], [], (i, true, false), i + 1) : RmExTr)]
  un := []

@[simp] theorem counterMach_mem (n : ℕ) : (counterMach n).mem = n := rfl

@[simp] theorem counterMach_start (n : ℕ) : (counterMach n).start = 0 := rfl

@[simp] theorem counterMach_un (n : ℕ) : (counterMach n).un = [] := rfl

theorem mem_counterMach_ex {n : ℕ} {t : RmExTr} (ht : t ∈ (counterMach n).ex) :
    ∃ i < n, t = (i, [], [], (i, false, true), 0) ∨ t = (i, [], [], (i, true, false), i + 1) := by
  simp only [counterMach, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  obtain ⟨i, hi, h⟩ := ht
  exact ⟨i, hi, h⟩

theorem counterMach_set_mem {n i : ℕ} (hi : i < n) :
    ((i, [], [], (i, false, true), 0) : RmExTr) ∈ (counterMach n).ex := by
  simp only [counterMach, List.mem_flatMap, List.mem_range, List.mem_cons]
  exact ⟨i, hi, Or.inl rfl⟩

theorem counterMach_clear_mem {n i : ℕ} (hi : i < n) :
    ((i, [], [], (i, true, false), i + 1) : RmExTr) ∈ (counterMach n).ex := by
  simp only [counterMach, List.mem_flatMap, List.mem_range, List.mem_cons]
  exact ⟨i, hi, Or.inr (Or.inl rfl)⟩

theorem counterMach_posBelow (n m : ℕ) : (counterMach n).PosBelow m := by
  refine ⟨fun t ht => ?_, fun t ht => by simp [counterMach] at ht, fun c hc => ?_⟩
  · obtain ⟨i, -, h | h⟩ := mem_counterMach_ex ht <;> subst h <;>
      intro p hp <;> simp [RmExTr.inG] at hp
  · simp only [counterMach, List.mem_singleton] at hc
    subst hc
    intro p hp
    simp [RmAcc.inG] at hp

/-! ### It accepts -/

theorem counterMach_accFromN_exists (n : ℕ) (W : List Bool) :
    ∀ m R i (μ : ℕ → Bool), R * (n + 1) + (n - i) ≤ m → i ≤ n → (∀ j < i, μ j = false) →
      (∀ j, n ≤ j → μ j = false) → (i = 0 ∨ ∃ p, i ≤ p ∧ p < n ∧ μ p = false) →
      ctrVal n μ + 2 ^ i + R = 2 ^ n → ∃ k, (counterMach n).AccFromN W k i μ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro R i μ hm hi hlow hhigh hex heq
    by_cases hall : ∀ j < n, μ j = true
    · -- every bit is set: accept, which is only possible in the state `0`
      have hi0 : i = 0 := by
        rcases hex with h | ⟨p, hip, hpn, hp⟩
        · exact h
        · rw [hall p hpn] at hp
          exact absurd hp (by simp)
      subst hi0
      refine ⟨1, RecAltMem.AccFromN.nil (c := (0, [], (List.range n).map fun j => (j, true)))
        (by simp [counterMach]) rfl (by intro p hp; simp [RmAcc.inG] at hp) ?_⟩
      intro p hp
      simp only [RmAcc.memG, List.mem_map, List.mem_range] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      exact ⟨by simpa using hj, by simpa using hall j hj⟩
    · push_neg at hall
      obtain ⟨p₀, hp₀n, hp₀⟩ := hall
      have hp₀f : μ p₀ = false := by
        cases hmu : μ p₀ with
        | false => rfl
        | true => exact absurd hmu hp₀
      have hfalse : ∃ p, i ≤ p ∧ p < n ∧ μ p = false := by
        rcases hex with h | h
        · exact ⟨p₀, by omega, hp₀n, hp₀f⟩
        · exact h
      obtain ⟨p, hip, hpn, hpf⟩ := hfalse
      have hin : i < n := by omega
      cases hmui : μ i with
      | false =>
        -- set the bit `i` and start the next increment
        have hval : ctrVal n (memUpd μ i true) = ctrVal n μ + 2 ^ i := ctrVal_set n μ i hin hmui
        have hlt := ctrVal_lt n (memUpd μ i true)
        have hR : 1 ≤ R := by omega
        have hsub : ∃ k, (counterMach n).AccFromN W k 0 (memUpd μ i true) := by
          refine IH ((R - 1) * (n + 1) + n) ?_ (R - 1) 0 (memUpd μ i true) le_rfl
            (by omega) (by omega) ?_ (Or.inl rfl) ?_
          · have h1 : (R - 1) * (n + 1) + (n + 1) = R * (n + 1) := by
              cases R with
              | zero => omega
              | succ R => simp; ring
            omega
          · intro j hj
            have hne : j ≠ i := by omega
            rw [memUpd_of_ne hne]
            exact hhigh j hj
          · rw [hval]
            have : (2 : ℕ) ^ 0 = 1 := by norm_num
            omega
        obtain ⟨k, hk⟩ := hsub
        refine ⟨k + 2, RecAltMem.AccFromN.ex (t := (i, [], [], (i, false, true), 0))
          (counterMach_set_mem hin) rfl (by intro q hq; simp [RmExTr.inG] at hq)
          (by intro q hq; simp [RmExTr.memG] at hq) (by simpa [RmExTr.wr, MemWrite.idx] using hin)
          (by simpa [RmExTr.wr, MemWrite.idx, MemWrite.old] using hmui) ?_⟩
        simpa [RmExTr.wr, MemWrite.idx, MemWrite.new, RmExTr.tgt] using hk
      | true =>
        -- clear the bit `i` and carry
        have hval : ctrVal n (memUpd μ i false) + 2 ^ i = ctrVal n μ :=
          ctrVal_clear n μ i hin hmui
        have hpi : i < p := by
          rcases Nat.lt_or_ge i p with h | h
          · exact h
          · have : p = i := by omega
            subst this
            rw [hmui] at hpf
            exact absurd hpf (by simp)
        have hsub : ∃ k, (counterMach n).AccFromN W k (i + 1) (memUpd μ i false) := by
          refine IH (R * (n + 1) + (n - (i + 1))) ?_ R (i + 1) (memUpd μ i false) le_rfl
            (by omega) ?_ ?_ (Or.inr ⟨p, by omega, hpn, ?_⟩) ?_
          · omega
          · intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
            · rw [memUpd_of_ne (by omega)]
              exact hlow j hlt
            · rw [memUpd_self]
          · intro j hj
            rw [memUpd_of_ne (by omega)]
            exact hhigh j hj
          · rw [memUpd_of_ne (by omega)]
            exact hpf
          · rw [pow_succ]
            omega
        obtain ⟨k, hk⟩ := hsub
        refine ⟨k + 2, RecAltMem.AccFromN.ex (t := (i, [], [], (i, true, false), i + 1))
          (counterMach_clear_mem hin) rfl (by intro q hq; simp [RmExTr.inG] at hq)
          (by intro q hq; simp [RmExTr.memG] at hq) (by simpa [RmExTr.wr, MemWrite.idx] using hin)
          (by simpa [RmExTr.wr, MemWrite.idx, MemWrite.old] using hmui) ?_⟩
        simpa [RmExTr.wr, MemWrite.idx, MemWrite.new, RmExTr.tgt] using hk

/-- **The counter accepts**: from the empty memory it counts up to `2 ^ n - 1`. -/
theorem counterMach_accepts (n : ℕ) (W : List Bool) : (counterMach n).Accepts W := by
  refine counterMach_accFromN_exists n W ((2 ^ n - 1) * (n + 1) + n) (2 ^ n - 1) 0
    (fun _ => false) le_rfl (by omega) (by omega) (fun _ _ => rfl) (Or.inl rfl) ?_
  have h0 : ctrVal n (fun _ => false) = 0 := ctrVal_of_all_false fun _ => rfl
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [h0]
  norm_num
  omega

/-! ### Every accepting computation is exponentially long -/

theorem counterMach_length_lower (n : ℕ) (W : List Bool) :
    ∀ {k q : ℕ} {μ : ℕ → Bool}, (counterMach n).AccFromN W k q μ →
      (2 : ℤ) ^ n - 1 - ctrVal n μ - (2 ^ q - 1) ≤ k := by
  intro k q μ h
  induction h with
  | @nil q μ c hc hq hin hg =>
    simp only [counterMach, List.mem_singleton] at hc
    subst hc
    have hq0 : q = 0 := by simpa [RmAcc.st] using hq.symm
    subst hq0
    have hall : ∀ j < n, μ j = true := by
      intro j hj
      have := hg (j, true) (by simp only [RmAcc.memG, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      exact this.2
    have hv := ctrVal_of_all_true hall
    have : ((ctrVal n μ : ℤ)) + 1 = 2 ^ n := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hv
    simp only [pow_zero]
    push_cast
    linarith
  | @ex k q μ t ht hq hin hg hw hu h' ih =>
    obtain ⟨i, hi, hset | hclear⟩ := mem_counterMach_ex ht
    · subst hset
      have hqi : q = i := by simpa [RmExTr.src] using hq.symm
      subst hqi
      have hmu : μ q = false := by simpa [RmExTr.wr, MemWrite.idx, MemWrite.old] using hu
      have hval : ctrVal n (memUpd μ q true) = ctrVal n μ + 2 ^ q := ctrVal_set n μ q hi hmu
      have hih : (2 : ℤ) ^ n - 1 - ctrVal n (memUpd μ q true) - (2 ^ (0:ℕ) - 1) ≤ k := by
        simpa [RmExTr.wr, MemWrite.idx, MemWrite.new, RmExTr.tgt] using ih
      rw [hval] at hih
      push_cast at hih ⊢
      linarith
    · subst hclear
      have hqi : q = i := by simpa [RmExTr.src] using hq.symm
      subst hqi
      have hmu : μ q = true := by simpa [RmExTr.wr, MemWrite.idx, MemWrite.old] using hu
      have hval : ctrVal n (memUpd μ q false) + 2 ^ q = ctrVal n μ := ctrVal_clear n μ q hi hmu
      have hih : (2 : ℤ) ^ n - 1 - ctrVal n (memUpd μ q false) - (2 ^ (q + 1) - 1) ≤ k := by
        simpa [RmExTr.wr, MemWrite.idx, MemWrite.new, RmExTr.tgt] using ih
      have hval' : ((ctrVal n (memUpd μ q false) : ℤ)) + 2 ^ q = ctrVal n μ := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hval
      rw [pow_succ] at hih
      push_cast at hih ⊢
      linarith
  | @un k₁ k₂ q μ t ht => exact absurd ht (by simp [counterMach])

/-- **Every accepting computation of the counter is worth at least `2 ^ n - 1` actions.** -/
theorem counterMach_accFromN_length {n : ℕ} {W : List Bool} {k : ℕ}
    (h : (counterMach n).AccFromN W k 0 (fun _ => false)) : 2 ^ n ≤ k + 1 := by
  have hb := counterMach_length_lower n W h
  have h0 : ctrVal n (fun _ => false) = 0 := ctrVal_of_all_false fun _ => rfl
  rw [h0] at hb
  simp only [pow_zero, Nat.cast_zero] at hb
  have : (2 : ℤ) ^ n ≤ (k : ℤ) + 1 := by linarith
  exact_mod_cast this

/-! ### The description, its size, and its plans -/

/-- The description is totally ordered. -/
theorem rmDom_counterMach_domOk (n m : ℕ) :
    SynClass.TO_HTN_root.domOk (rmDom (counterMach n) m) := rmDom_domOk m

theorem length_counterMach_ex (n : ℕ) : (counterMach n).ex.length = 2 * n := by
  simp only [counterMach]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.length_append, ih, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_cons, List.length_nil]
    omega

theorem rmBudget_counterMach (n : ℕ) : rmBudget (counterMach n) = 4 + 2 * n := by
  have hex : ((counterMach n).ex.map fun t => t.inG.length + t.memG.length).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨i, -, h | h⟩ := mem_counterMach_ex ht <;> subst h <;> simp [RmExTr.inG, RmExTr.memG]
  have hacc : ((counterMach n).acc.map fun c => c.inG.length + c.memG.length).sum = n := by
    simp [counterMach, RmAcc.inG, RmAcc.memG]
  simp only [rmBudget, counterMach_mem, counterMach_un, hex, hacc, List.map_nil, List.sum_nil]
  omega

theorem rmNumActs_counterMach (n : ℕ) : rmNumActs (counterMach n) = 8 * n + 8 := by
  have hacc : (counterMach n).acc.length = 1 := rfl
  have hun : (counterMach n).un.length = 0 := rfl
  rw [rmNumActs, length_counterMach_ex, hacc, hun]
  omega

theorem rmConst_counterMach (n : ℕ) : rmConst (counterMach n) = 16 * n ^ 2 + 72 * n + 44 := by
  have hacc : (counterMach n).acc.length = 1 := rfl
  have hun : (counterMach n).un.length = 0 := rfl
  rw [rmConst, rmNumActs_counterMach, rmBudget_counterMach, length_counterMach_ex, hacc, hun]
  ring

/-- **The description of the counter has quadratic size** — while its plans are exponentially
long. -/
theorem size_rmDom_counterMach_le (n m : ℕ) :
    (rmDom (counterMach n) m).size ≤ 16 * n ^ 2 + 72 * n + 44 := by
  have h := size_rmDom_le (M := counterMach n) m
  rw [rmConst_counterMach] at h
  exact h

/-- **The encoded problem of the counter is solvable.** -/
theorem solvable_rmDom_counterMach (n : ℕ) (W : List Bool) :
    Solvable (rmDom (counterMach n) W.length) (posEnc W) :=
  (solvable_rmDom_iff (counterMach_posBelow n W.length)).2 (counterMach_accepts n W)

/-- **Every plan of the encoded problem has at least `2 ^ n` actions.** -/
theorem length_ge_of_plan_counterMach {n : ℕ} {W : List Bool} {as : List ℕ}
    (hy : (rmDom (counterMach n) W.length).toDomain.YieldSeq [Sum.inr 0] as)
    (happ : (rmDom (counterMach n) W.length).toDomain.SeqApplicable as
      {f | f ∈ posFacts W}) : 2 ^ n ≤ as.length := by
  obtain ⟨k, hlen, hacc⟩ := accFromN_of_plan (counterMach_posBelow n W.length) hy happ
  have := counterMach_accFromN_length (n := n) (W := W) (k := k) (by simpa using hacc)
  omega

/-- **A totally ordered, recursive description of quadratic size, solvable, all of whose plans
are exponentially long.**  This is what the recursive encoding buys over the counted one: the
description names neither the steps nor the levels of the computation. -/
theorem rmDom_counterMach_exponential (n : ℕ) (W : List Bool) :
    (rmDom (counterMach n) W.length).size ≤ 16 * n ^ 2 + 72 * n + 44 ∧
      Solvable (rmDom (counterMach n) W.length) (posEnc W) ∧
      ∀ as : List ℕ, (rmDom (counterMach n) W.length).toDomain.YieldSeq [Sum.inr 0] as →
        (rmDom (counterMach n) W.length).toDomain.SeqApplicable as {f | f ∈ posFacts W} →
        2 ^ n ≤ as.length :=
  ⟨size_rmDom_counterMach_le n W.length, solvable_rmDom_counterMach n W,
    fun _ hy happ => length_ge_of_plan_counterMach hy happ⟩

/-! ### The counters as a uniform family

The counter is not a hard language — it accepts every word — but it *is* a uniform family in the
sense of `HTN.Syn.UniRecMem`, and so an example of one whose problems have only exponentially
long plans.  That is the property the padded families of
`HtnComplexity/Complexity/AltMemUniform.lean` cannot have: their plans have one action per
bit of the padded input. -/

theorem primrec_counterMach : RecMachFamPrimrec counterMach := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Primrec.id.of_eq fun _ => rfl
  · exact (Primrec.const 0).of_eq fun _ => rfl
  · have h : Primrec fun n : ℕ =>
        [((0 : ℕ), ([] : List InLit), (List.range n).map fun j => ((j, true) : MemLit))] := by
      refine Primrec.list_cons.comp ?_ (Primrec.const [])
      refine Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const []) ?_)
      exact Primrec.list_map Primrec.list_range
        (Primrec.pair Primrec.snd (Primrec.const true))
    exact h.of_eq fun _ => rfl
  · have h : Primrec fun n : ℕ => (List.range n).flatMap fun i =>
        [((i, [], [], (i, false, true), 0) : RmExTr),
          ((i, [], [], (i, true, false), i + 1) : RmExTr)] := by
      refine Primrec.list_flatMap Primrec.list_range ?_
      have ii : Primrec fun w : ℕ × ℕ => w.2 := Primrec.snd
      have hsucc : Primrec fun w : ℕ × ℕ => w.2 + 1 :=
        Primrec.nat_add.comp ii (Primrec.const 1)
      refine Primrec.list_cons.comp ?_ (Primrec.list_cons.comp ?_ (Primrec.const []))
      · exact Primrec.pair ii (Primrec.pair (Primrec.const []) (Primrec.pair (Primrec.const [])
          (Primrec.pair (Primrec.pair ii (Primrec.pair (Primrec.const false) (Primrec.const true)))
            (Primrec.const 0))))
      · exact Primrec.pair ii (Primrec.pair (Primrec.const []) (Primrec.pair (Primrec.const [])
          (Primrec.pair (Primrec.pair ii (Primrec.pair (Primrec.const true) (Primrec.const false)))
            hsucc)))
    exact h.of_eq fun _ => rfl
  · exact (Primrec.const []).of_eq fun _ => rfl

/-- **The uniform family of binary counters.** -/
noncomputable def counterFam : UniRecMem where
  mach := counterMach
  bound := Polynomial.C 16 * Polynomial.X ^ 2 + Polynomial.C 72 * Polynomial.X + Polynomial.C 44
  mach_primrec := primrec_counterMach
  pos_below := fun n => counterMach_posBelow n n
  dom_size := fun n => by
    rw [rmConst_counterMach]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    omega

/-- Its language is the trivial one: the counter accepts every word. -/
theorem counterFam_L (w : List Bool) : counterFam.L w := counterMach_accepts w.length w

/-- **A polynomial-time hardness family, in `TO-HTN` with a rooted instance, all of whose plans
are exponentially long in the length of the word.**  The language is trivial — the point is the
shape of the encoding, not the language. -/
theorem counterFam_plans_exponential {w : List Bool} {as : List ℕ}
    (hy : (counterFam.dom w.length).toDomain.YieldSeq [Sum.inr 0] as)
    (happ : (counterFam.dom w.length).toDomain.SeqApplicable as {f | f ∈ posFacts w}) :
    2 ^ w.length ≤ as.length :=
  length_ge_of_plan_counterMach (n := w.length) hy happ

end Syn

end HTN
