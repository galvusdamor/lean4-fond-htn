import HtnComplexity.TMEnc.TMEncFixPlanData
import HtnComplexity.TMEnc.TMEncPrefix
/-!
# The three streams of a solution plan run in lock-step

This is the *alignment* half of the soundness direction: the hierarchy of the repaired encoding
says **what** the three streams of a solution plan are
(`HTN.TMEnc.isSolutionPlanFix_normalForm`), and the semaphore protocol — i.e. executability —
says **how they are aligned**.

The statement proved here is the heart of it:

`HTN.TMEnc.lockstep` — at the end of the `n`-th cell of the tape *every one of the `K + 1` cell
counters has answered exactly `n` requests on the `check` channel and `n` on the `sync`
channel*; no counter can run ahead of, or lag behind, the tape.

The proof is a counting argument.  At any prefix `p` of the plan write `#call x`, `#start x`,
`#respond x`, `#wait x` for the numbers of the four actions of the channel `x`.  Only the tape
issues (`call`, `wait`) and only the counters answer (`start`, `respond`), so

* `#call x` and `#wait x` are read off the tape part of `p` (`HTN.TMEnc.tapePrefix`),
* `#start x` and `#respond x` are the sums over the counters.

The semaphore inequalities of `HtnComplexity/TMEnc/TMEncPrefix.lean` give
`#start x ≤ #call x` and `#wait x ≤ #respond x`, and inside a counter a `respond` never precedes
its `start` (`HTN.TMEnc.countP_isRespond_le_isStart_counterRun`), so at a moment at which the
tape has issued and waited for exactly `k` requests, exactly `k` of them have been answered
(`HTN.TMEnc.countP_isStart_eq_of_tape`).  Two families of such moments — the end of a cell and
the end of the `check` half of a cell — then force, by induction over the cells and the
alternation of the two channels inside a counter
(`HTN.TMEnc.countP_prefix_counterRun`), that all counters advance by exactly one cell per cell of
the tape.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Two counting lemmas about lists of naturals -/

lemma mul_length_le_sum {L : List ℕ} {n : ℕ} (h : ∀ x ∈ L, n ≤ x) : n * L.length ≤ L.sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : n ≤ a := h a (by simp)
      have ht : n * t.length ≤ t.sum := ih fun x hx => h x (by simp [hx])
      simp only [List.length_cons, List.sum_cons]
      nlinarith [Nat.mul_succ n t.length]

lemma sum_le_mul_length {L : List ℕ} {n : ℕ} (h : ∀ x ∈ L, x ≤ n) : L.sum ≤ n * L.length := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : a ≤ n := h a (by simp)
      have ht : t.sum ≤ n * t.length := ih fun x hx => h x (by simp [hx])
      simp only [List.length_cons, List.sum_cons]
      nlinarith [Nat.mul_succ n t.length]

/-- A list of naturals all at least `n` whose sum is `n` times its length is constant. -/
lemma all_eq_of_sum_of_ge {L : List ℕ} {n : ℕ} (h : ∀ x ∈ L, n ≤ x)
    (hs : L.sum = n * L.length) : ∀ x ∈ L, x = n := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : n ≤ a := h a (by simp)
      have ht : n * t.length ≤ t.sum := mul_length_le_sum fun x hx => h x (by simp [hx])
      simp only [List.length_cons, List.sum_cons, Nat.mul_succ] at hs
      have ha' : a = n := by omega
      have hts : t.sum = n * t.length := by omega
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ha'
      · exact ih (fun y hy => h y (by simp [hy])) hts x hx'

/-- A list of naturals all at most `n` whose sum is `n` times its length is constant. -/
lemma all_eq_of_sum_of_le {L : List ℕ} {n : ℕ} (h : ∀ x ∈ L, x ≤ n)
    (hs : L.sum = n * L.length) : ∀ x ∈ L, x = n := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : a ≤ n := h a (by simp)
      have ht : t.sum ≤ n * t.length := sum_le_mul_length fun x hx => h x (by simp [hx])
      simp only [List.length_cons, List.sum_cons, Nat.mul_succ] at hs
      have ha' : a = n := by omega
      have hts : t.sum = n * t.length := by omega
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ha'
      · exact ih (fun y hy => h y (by simp [hy])) hts x hx'

/-! ### The parts of a split are prefixes of counter runs -/

variable {D : SolutionPlanData N w K}

/-- Every part of a split of a prefix of the plan is a prefix of the run of a cell counter. -/
lemma isPrefix_counterRun_of_mem_parts {p : List (TMAct Q Γ)}
    {parts : List (List (TMAct Q Γ))} {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    {l : List (TMAct Q Γ)} (hl : l ∈ parts) :
    ∃ (d e : ℕ) (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ),
      (∀ t < K, StepDecision N w K (P t)) ∧ l <+: counterRun Q Γ K d e P c := by
  obtain ⟨l', hl', hpre⟩ := exists_right_of_forall₂ h.parts_prefix hl
  obtain ⟨d, e, P, c, hP, rfl⟩ := D.isCounter l' hl'
  exact ⟨d, e, P, c, hP, hpre⟩

/-- A part of a split answers at most one more request on `check` than on `sync`. -/
lemma part_alternates {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    {l : List (TMAct Q Γ)} (hl : l ∈ parts) :
    l.countP (isStart SyncKind.sync) ≤ l.countP (isStart SyncKind.check) ∧
      l.countP (isStart SyncKind.check) ≤ l.countP (isStart SyncKind.sync) + 1 := by
  obtain ⟨d, e, P, c, hP, hpre⟩ := isPrefix_counterRun_of_mem_parts h hl
  exact countP_prefix_counterRun (N := N) (w := w) hP hpre

/-- A part of a split has started every answer it has given. -/
lemma part_respond_le_start {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    (x : SyncKind) {l : List (TMAct Q Γ)} (hl : l ∈ parts) :
    l.countP (isRespond x) ≤ l.countP (isStart x) := by
  obtain ⟨d, e, P, c, hP, hpre⟩ := isPrefix_counterRun_of_mem_parts h hl
  exact countP_isRespond_le_isStart_counterRun (N := N) (w := w) x hP hpre

/-- A part of a split issues no request on a cell channel. -/
lemma part_no_call {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    {x : SyncKind} (hx : x ≠ SyncKind.head) {l : List (TMAct Q Γ)} (hl : l ∈ parts) :
    l.countP (isCall x) = 0 := by
  obtain ⟨d, e, P, c, hP, hpre⟩ := isPrefix_counterRun_of_mem_parts h hl
  have := hpre.sublist.countP_le (p := isCall x)
  rw [countP_isCall_counterRun hx hP] at this
  omega

lemma part_no_wait {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    {x : SyncKind} (hx : x ≠ SyncKind.head) {l : List (TMAct Q Γ)} (hl : l ∈ parts) :
    l.countP (isWait x) = 0 := by
  obtain ⟨d, e, P, c, hP, hpre⟩ := isPrefix_counterRun_of_mem_parts h hl
  have := hpre.sublist.countP_le (p := isWait x)
  rw [countP_isWait_counterRun hx hP] at this
  omega

/-! ### Reading the four counts off a split -/

lemma head_part_countP_isStart {ph : List (TMAct Q Γ)} (hph : ph <+: headStream Q Γ K)
    {x : SyncKind} (hx : x ≠ SyncKind.head) : ph.countP (isStart x) = 0 := by
  have := hph.sublist.countP_le (p := isStart x)
  rw [countP_isStart_headStream hx] at this
  omega

lemma head_part_countP_isRespond {ph : List (TMAct Q Γ)} (hph : ph <+: headStream Q Γ K)
    {x : SyncKind} (hx : x ≠ SyncKind.head) : ph.countP (isRespond x) = 0 := by
  have := hph.sublist.countP_le (p := isRespond x)
  rw [countP_isRespond_headStream hx] at this
  omega

lemma head_part_countP_isCall {ph : List (TMAct Q Γ)} (hph : ph <+: headStream Q Γ K)
    {x : SyncKind} : ph.countP (isCall x) = 0 := by
  have := hph.sublist.countP_le (p := isCall x)
  rw [countP_isCall_headStream (x := x)] at this
  omega

lemma head_part_countP_isWait {ph : List (TMAct Q Γ)} (hph : ph <+: headStream Q Γ K)
    {x : SyncKind} : ph.countP (isWait x) = 0 := by
  have := hph.sublist.countP_le (p := isWait x)
  rw [countP_isWait_headStream (x := x)] at this
  omega

lemma tape_part_countP_isStart {sym : ℕ → Option Γ} {pt : List (TMAct Q Γ)}
    (hpt : pt <+: tapeStream Q Γ K sym) {x : SyncKind} : pt.countP (isStart x) = 0 := by
  have := hpt.sublist.countP_le (p := isStart x)
  rw [show tapeStream Q Γ K sym = tapePrefix Q Γ K ((K + 1) * (K + 1)) sym from rfl,
    countP_isStart_tapePrefix] at this
  omega

lemma tape_part_countP_isRespond {sym : ℕ → Option Γ} {pt : List (TMAct Q Γ)}
    (hpt : pt <+: tapeStream Q Γ K sym) {x : SyncKind} : pt.countP (isRespond x) = 0 := by
  have := hpt.sublist.countP_le (p := isRespond x)
  rw [show tapeStream Q Γ K sym = tapePrefix Q Γ K ((K + 1) * (K + 1)) sym from rfl,
    countP_isRespond_tapePrefix] at this
  omega

/-- **The answers given in a prefix of the plan are the answers of the counters.** -/
lemma countP_isStart_eq_sum {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    {x : SyncKind} (hx : x ≠ SyncKind.head) :
    p.countP (isStart x) = (parts.map fun l => l.countP (isStart x)).sum := by
  rw [countP_of_isPlanSplit h, head_part_countP_isStart h.2.1 hx,
    tape_part_countP_isStart h.tape_prefix]
  omega

lemma countP_isRespond_eq_sum {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    {x : SyncKind} (hx : x ≠ SyncKind.head) :
    p.countP (isRespond x) = (parts.map fun l => l.countP (isRespond x)).sum := by
  rw [countP_of_isPlanSplit h, head_part_countP_isRespond h.2.1 hx,
    tape_part_countP_isRespond h.tape_prefix]
  omega

/-- **The requests issued in a prefix of the plan are the requests of the tape.** -/
lemma countP_isCall_eq_tape {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    {x : SyncKind} (hx : x ≠ SyncKind.head) :
    p.countP (isCall x) = pt.countP (isCall x) := by
  have hzero : (parts.map fun l => l.countP (isCall x)).sum = 0 := by
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    exact part_no_call h hx hl
  rw [countP_of_isPlanSplit h, head_part_countP_isCall h.2.1, hzero]
  omega

lemma countP_isWait_eq_tape {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    {x : SyncKind} (hx : x ≠ SyncKind.head) :
    p.countP (isWait x) = pt.countP (isWait x) := by
  have hzero : (parts.map fun l => l.countP (isWait x)).sum = 0 := by
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    exact part_no_wait h hx hl
  rw [countP_of_isPlanSplit h, head_part_countP_isWait h.2.1, hzero]
  omega

/-! ### At a moment of the tape, every request issued has been answered -/

/-- **The moment lemma.**  If in a prefix `p` of the plan the tape has issued `k` requests on the
channel `x` and has waited for all of them, then exactly `k` answers have been given. -/
theorem countP_isStart_eq_of_tape {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)} (hp : p <+: D.as₁)
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    {x : SyncKind} (hx : x ≠ SyncKind.head) {k : ℕ}
    (hcall : pt.countP (isCall x) = k) (hwait : pt.countP (isWait x) = k) :
    p.countP (isStart x) = k := by
  obtain ⟨r, hr⟩ := hp
  have hpq : D.as₁ ++ [TMAct.check (TMFact.st D.f)] = p ++ (r ++ [TMAct.check (TMFact.st D.f)]) := by
    rw [← hr]; simp
  obtain ⟨h₁, h₂, h₃, h₄⟩ := countP_prefix_alternates_fix x D.isPlan hpq
  have hcc : p.countP (isCall x) = k := by rw [countP_isCall_eq_tape h hx, hcall]
  have hww : p.countP (isWait x) = k := by rw [countP_isWait_eq_tape h hx, hwait]
  have hrs : p.countP (isRespond x) ≤ p.countP (isStart x) := by
    rw [countP_isStart_eq_sum h hx, countP_isRespond_eq_sum h hx]
    exact List.sum_le_sum fun l hl => part_respond_le_start h x hl
  omega

/-! ### The moments -/

/-- The tape stream, cut at the end of the `check` half of cell `n`. -/
lemma tapeStream_cut_check {sym : ℕ → Option Γ} {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    ∃ rest : List (TMAct Q Γ), tapeStream Q Γ K sym =
      (tapePrefix Q Γ K n sym ++ cellCheckPart Q Γ K (sym n)) ++ rest := by
  have hsplit := tapeStream_split (Q := Q) (Γ := Γ) (K := K) (sym := sym) (n := n) (by omega)
  have hR : (K + 1) * (K + 1) - n = 1 + ((K + 1) * (K + 1) - n - 1) := by omega
  rw [hsplit, hR, roundStream_add, roundStream_one]
  refine ⟨cellSyncPart Q Γ K ++ roundStream ((K + 1) * (K + 1) - n - 1)
    fun m => cellRun Q Γ K (sym (n + (1 + m))), ?_⟩
  rw [cellRun_split]
  simp [List.append_assoc]

/-- **The moment at the end of cell `n`**: a prefix of the plan at which the tape has completed
its first `n` cells, and at which therefore every one of the `n * (K+1)` requests on either cell
channel has been answered. -/
theorem exists_moment_cell (D : SolutionPlanData N w K) {n : ℕ} (hn : n ≤ (K + 1) * (K + 1)) :
    ∃ (p : List (TMAct Q Γ)) (parts : List (List (TMAct Q Γ))) (ph : List (TMAct Q Γ)),
      p <+: D.as₁ ∧
        IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph
          (tapePrefix Q Γ K n D.sym) ∧
        p.countP (isStart SyncKind.check) = n * (K + 1) ∧
        p.countP (isStart SyncKind.sync) = n * (K + 1) := by
  obtain ⟨p, parts, ph, hp, hsplit⟩ :=
    exists_isPlanSplit_of_tape D.hil D.hac D.hbs (tapeStream_split hn)
  refine ⟨p, parts, ph, hp, hsplit, ?_, ?_⟩
  · exact countP_isStart_eq_of_tape hp hsplit (by simp) (by simp) (by simp)
  · exact countP_isStart_eq_of_tape hp hsplit (by simp) (by simp) (by simp)

/-- **The moment at the end of the `check` half of cell `n`**: the tape has issued and waited for
all `(n+1) * (K+1)` requests on the `check` channel, but for none of the requests on the `sync`
channel of cell `n`. -/
theorem exists_moment_check (D : SolutionPlanData N w K) {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    ∃ p : List (TMAct Q Γ), p <+: D.as₁ ∧
        p.countP (isStart SyncKind.check) = (n + 1) * (K + 1) ∧
        p.countP (isStart SyncKind.sync) = n * (K + 1) := by
  obtain ⟨rest, hcut⟩ := tapeStream_cut_check (Q := Q) (Γ := Γ) (K := K) (sym := D.sym) hn
  obtain ⟨p, parts, ph, hp, hsplit⟩ := exists_isPlanSplit_of_tape D.hil D.hac D.hbs hcut
  refine ⟨p, hp, ?_, ?_⟩
  · refine countP_isStart_eq_of_tape hp hsplit (by simp) ?_ ?_ <;>
      rw [List.countP_append] <;> simp <;> ring
  · refine countP_isStart_eq_of_tape hp hsplit (by simp) ?_ ?_ <;>
      rw [List.countP_append] <;> simp

/-! ### The lock-step induction -/

/-- The counters of a split have each answered `a` requests on the `check` channel and `b` on the
`sync` channel. -/
def PartsAt (parts : List (List (TMAct Q Γ))) (a b : ℕ) : Prop :=
  ∀ l ∈ parts, l.countP (isStart SyncKind.check) = a ∧ l.countP (isStart SyncKind.sync) = b

lemma parts_length {p : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))}
    {ph pt : List (TMAct Q Γ)}
    (h : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt) :
    parts.length = K + 1 := by
  rw [h.parts_prefix.length_eq, D.card]

/-- **The step of the lock-step induction, at the end of the `check` half of a cell.** -/
lemma lockstep_check (D : SolutionPlanData N w K) {n : ℕ} (hn : n < (K + 1) * (K + 1))
    (IH : ∀ (p : List (TMAct Q Γ)) (parts : List (List (TMAct Q Γ))) (ph pt : List (TMAct Q Γ)),
      p <+: D.as₁ → IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt →
        p.countP (isStart SyncKind.check) = n * (K + 1) →
        p.countP (isStart SyncKind.sync) = n * (K + 1) → PartsAt parts n n)
    (p : List (TMAct Q Γ)) (parts : List (List (TMAct Q Γ))) (ph pt : List (TMAct Q Γ))
    (hp : p <+: D.as₁) (hsplit : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt)
    (hcheck : p.countP (isStart SyncKind.check) = (n + 1) * (K + 1))
    (hsync : p.countP (isStart SyncKind.sync) = n * (K + 1)) : PartsAt parts (n + 1) n := by
  obtain ⟨p₀, parts₀, ph₀, hp₀, -, hc₀, hs₀⟩ := exists_moment_cell D (le_of_lt hn)
  have hle : p₀ <+: p := by
    rcases List.prefix_or_prefix_of_prefix hp₀ hp with h | h
    · exact h
    · have hcount := h.sublist.countP_le (p := isStart SyncKind.check)
      rw [hcheck, hc₀] at hcount
      nlinarith
  obtain ⟨parts', ph', pt', hsplit', hall⟩ := hsplit.restrict hle
  have hpa := IH p₀ parts' ph' pt' hp₀ hsplit' hc₀ hs₀
  have hlen : parts.length = K + 1 := parts_length hsplit
  -- every counter has answered at least `n` requests on the `sync` channel
  have hge : ∀ y ∈ parts.map fun l => l.countP (isStart SyncKind.sync), n ≤ y := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    obtain ⟨l₀, hl₀, hpre⟩ := exists_left_of_forall₂ hall hl
    have hcount := hpre.sublist.countP_le (p := isStart SyncKind.sync)
    rw [(hpa l₀ hl₀).2] at hcount
    exact hcount
  have hsum : (parts.map fun l => l.countP (isStart SyncKind.sync)).sum =
      n * (parts.map fun l => l.countP (isStart SyncKind.sync)).length := by
    rw [← countP_isStart_eq_sum hsplit (by simp), hsync, List.length_map, hlen]
  have hallsync := all_eq_of_sum_of_ge hge hsum
  -- hence exactly `n + 1` on the `check` channel
  have hle' : ∀ y ∈ parts.map fun l => l.countP (isStart SyncKind.check), y ≤ n + 1 := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    have h₂ := (part_alternates hsplit hl).2
    have h₃ := hallsync (l.countP (isStart SyncKind.sync)) (List.mem_map_of_mem hl)
    omega
  have hsum' : (parts.map fun l => l.countP (isStart SyncKind.check)).sum =
      (n + 1) * (parts.map fun l => l.countP (isStart SyncKind.check)).length := by
    rw [← countP_isStart_eq_sum hsplit (by simp), hcheck, List.length_map, hlen]
  have hallcheck := all_eq_of_sum_of_le hle' hsum'
  intro l hl
  exact ⟨hallcheck _ (List.mem_map_of_mem hl), hallsync _ (List.mem_map_of_mem hl)⟩

/-- **The lock-step theorem.**  At a moment of a solution plan at which `n * (K+1)` requests have
been answered on each of the two cell channels — that is, at the end of the `n`-th cell of the
tape — *every one of the `K + 1` cell counters has answered exactly `n` of them on each
channel*. -/
theorem lockstep (D : SolutionPlanData N w K) :
    ∀ n : ℕ, n ≤ (K + 1) * (K + 1) →
      ∀ (p : List (TMAct Q Γ)) (parts : List (List (TMAct Q Γ))) (ph pt : List (TMAct Q Γ)),
        p <+: D.as₁ → IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt →
          p.countP (isStart SyncKind.check) = n * (K + 1) →
          p.countP (isStart SyncKind.sync) = n * (K + 1) → PartsAt parts n n := by
  intro n
  induction n with
  | zero =>
      intro _ p parts ph pt _ hsplit hcheck hsync
      have hc : (parts.map fun l => l.countP (isStart SyncKind.check)).sum = 0 := by
        rw [← countP_isStart_eq_sum hsplit (by simp), hcheck]; ring
      have hs : (parts.map fun l => l.countP (isStart SyncKind.sync)).sum = 0 := by
        rw [← countP_isStart_eq_sum hsplit (by simp), hsync]; ring
      intro l hl
      constructor
      · exact all_eq_of_sum_of_ge (fun _ _ => Nat.zero_le _) (by simpa using hc) _
          (List.mem_map_of_mem hl)
      · exact all_eq_of_sum_of_ge (fun _ _ => Nat.zero_le _) (by simpa using hs) _
          (List.mem_map_of_mem hl)
  | succ n ih =>
      intro hn p parts ph pt hp hsplit hcheck hsync
      have hn' : n < (K + 1) * (K + 1) := by omega
      -- the moment at the end of the `check` half of cell `n`
      obtain ⟨p₁, hp₁, hc₁, hs₁⟩ := exists_moment_check D hn'
      have hle : p₁ <+: p := by
        rcases List.prefix_or_prefix_of_prefix hp₁ hp with h | h
        · exact h
        · have hcount := h.sublist.countP_le (p := isStart SyncKind.sync)
          rw [hsync, hs₁] at hcount
          nlinarith
      obtain ⟨parts', ph', pt', hsplit', hall⟩ := hsplit.restrict hle
      have hpa : PartsAt parts' (n + 1) n :=
        lockstep_check D hn' (ih (by omega)) p₁ parts' ph' pt' hp₁ hsplit' hc₁ hs₁
      have hlen : parts.length = K + 1 := parts_length hsplit
      have hge : ∀ y ∈ parts.map fun l => l.countP (isStart SyncKind.check), n + 1 ≤ y := by
        intro y hy
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
        obtain ⟨l₀, hl₀, hpre⟩ := exists_left_of_forall₂ hall hl
        have hcount := hpre.sublist.countP_le (p := isStart SyncKind.check)
        rw [(hpa l₀ hl₀).1] at hcount
        exact hcount
      have hsum : (parts.map fun l => l.countP (isStart SyncKind.check)).sum =
          (n + 1) * (parts.map fun l => l.countP (isStart SyncKind.check)).length := by
        rw [← countP_isStart_eq_sum hsplit (by simp), hcheck, List.length_map, hlen]
      have hallcheck := all_eq_of_sum_of_ge hge hsum
      have hle' : ∀ y ∈ parts.map fun l => l.countP (isStart SyncKind.sync), y ≤ n + 1 := by
        intro y hy
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
        have h₁ := (part_alternates hsplit hl).1
        have h₃ := hallcheck (l.countP (isStart SyncKind.check)) (List.mem_map_of_mem hl)
        omega
      have hsum' : (parts.map fun l => l.countP (isStart SyncKind.sync)).sum =
          (n + 1) * (parts.map fun l => l.countP (isStart SyncKind.sync)).length := by
        rw [← countP_isStart_eq_sum hsplit (by simp), hsync, List.length_map, hlen]
      have hallsync := all_eq_of_sum_of_le hle' hsum'
      intro l hl
      exact ⟨hallcheck _ (List.mem_map_of_mem hl), hallsync _ (List.mem_map_of_mem hl)⟩

/-- **The lock-step theorem, in the form it will be used.**  At the end of the `n`-th cell of the
tape of a solution plan, each of the `K + 1` cell counters has answered exactly `n` requests on
the `check` channel and `n` on the `sync` channel: the counters advance by exactly one of their
own cells per cell of the tape. -/
theorem exists_lockstep_moment (D : SolutionPlanData N w K) {n : ℕ} (hn : n ≤ (K + 1) * (K + 1)) :
    ∃ (p : List (TMAct Q Γ)) (parts : List (List (TMAct Q Γ))) (ph : List (TMAct Q Γ)),
      p <+: D.as₁ ∧
        IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph
          (tapePrefix Q Γ K n D.sym) ∧ parts.length = K + 1 ∧ PartsAt parts n n := by
  obtain ⟨p, parts, ph, hp, hsplit, hc, hs⟩ := exists_moment_cell D hn
  exact ⟨p, parts, ph, hp, hsplit, parts_length hsplit,
    lockstep D n hn p parts ph _ hp hsplit hc hs⟩

/-- The same statement, read off a solution plan directly. -/
theorem exists_lockstep_moment_of_isSolutionPlan (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    {as : List (TMAct Q Γ)} (h : (problemFix N w K).IsSolutionPlan as) {n : ℕ}
    (hn : n ≤ (K + 1) * (K + 1)) :
    ∃ (D : SolutionPlanData N w K) (p : List (TMAct Q Γ)) (parts : List (List (TMAct Q Γ)))
      (ph : List (TMAct Q Γ)),
      as = D.as₁ ++ [TMAct.check (TMFact.st D.f)] ∧ p <+: D.as₁ ∧
        IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph
          (tapePrefix Q Γ K n D.sym) ∧ parts.length = K + 1 ∧ PartsAt parts n n := by
  obtain ⟨D, hD⟩ := exists_planData hw hwK h
  obtain ⟨p, parts, ph, hp, hsplit, hlen, hpa⟩ := exists_lockstep_moment D hn
  exact ⟨D, p, parts, ph, hD, hp, hsplit, hlen, hpa⟩

end TMEnc

end HTN
