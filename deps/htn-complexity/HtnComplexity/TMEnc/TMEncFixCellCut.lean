import HtnComplexity.TMEnc.TMEncFixLockstep
import HtnComplexity.TMEnc.TMEncFixCounterShape
/-!
# Cutting a solution plan at the `assert` of a cell

The lock-step theorem (`HTN.TMEnc.lockstep`) counts, at the end of the `n`-th cell of the tape,
how many requests each cell counter has answered.  This file turns that count into a *position*:

* `HTN.TMEnc.parts_full_counts` — at such a moment each counter has also *responded* `n` times on
  the `sync` channel, so — the first action of a cell of a counter being `start check` and its
  last one `respond sync` — the part of the plan that a counter has executed is **exactly** the
  stream of its first `n` cells (`HTN.TMEnc.prefix_counterRun_eq`);
* `HTN.TMEnc.exists_cellCut` — **a solution plan cut at the `assert` of the cell `n`**:

      as₁ = u ++ assert (sym n) :: (m ++ v)

  where the piece `m` is an interleaving of the *`n`-th cell of every one of the `K + 1`
  counters* with the rest of the tape's cell `n` and with a piece of the head counter.

Everything the counters do during the cell `n` of the tape therefore happens inside `m`, i.e.
after the tape has written the symbol `sym n` and before it writes `sym (n+1)`.  This is what
lets the next step read off *which* symbol a counter tests.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The tape, cut at an `assert` -/

/-- The actions of a cell of the tape after the `assert`. -/
def cellTail (Q Γ : Type) (K : ℕ) : List (TMAct Q Γ) :=
  acquireActs Q Γ SyncKind.head ++
    ((roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.check) ++
      (roundStream (K + 1) fun _ => acquireActs Q Γ SyncKind.sync))

lemma cellRun_eq_cons {c : Option Γ} :
    cellRun Q Γ K c = TMAct.assert c :: cellTail Q Γ K := rfl

/-- The first `n + 1` cells of the tape, cut at the `assert` of the last one. -/
lemma tapePrefix_succ {sym : ℕ → Option Γ} (n : ℕ) :
    tapePrefix Q Γ K (n + 1) sym =
      tapePrefix Q Γ K n sym ++ TMAct.assert (sym n) :: cellTail Q Γ K := by
  rw [tapePrefix, roundStream_succ, ← tapePrefix, cellRun_eq_cons]

/-- No action of the tape is an `assert` of another cell, and none is a `step`. -/
lemma cellTail_filter {f : TMAct Q Γ → Bool}
    (hf : ∀ x : SyncKind, f (TMAct.call x) = false ∧ f (TMAct.wait x) = false) :
    (cellTail Q Γ K).filter f = [] := by
  have hacq : ∀ x : SyncKind, (acquireActs Q Γ x).filter f = [] := by
    intro x
    simp [acquireActs, (hf x).1, (hf x).2]
  have hround : ∀ (R : ℕ) (x : SyncKind),
      (roundStream R fun _ => acquireActs Q Γ x).filter f = [] := by
    intro R x
    induction R with
    | zero => simp
    | succ R ih => rw [roundStream_succ, List.filter_append, ih, hacq x]; rfl
  simp [cellTail, List.filter_append, hacq, hround]

/-! ### The plan as an interleaving -/

/-- The three streams of a solution plan. -/
lemma SolutionPlanData.planInter (D : SolutionPlanData N w K) :
    PlanInter D.ass (headStream Q Γ K) (tapeStream Q Γ K D.sym) D.as₁ :=
  ⟨D.ac, D.bs, D.hil, D.hac, D.hbs⟩

lemma isPlanSplit_of_planInter {D : SolutionPlanData N w K} {parts : List (List (TMAct Q Γ))}
    {ph pt p : List (TMAct Q Γ)} (h : PlanInter parts ph pt p)
    (hparts : List.Forall₂ (· <+: ·) parts D.ass) (hph : ph <+: headStream Q Γ K)
    (hpt : pt <+: tapeStream Q Γ K D.sym) :
    IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph pt :=
  ⟨hparts, hph, hpt, h⟩

/-! ### At a moment, every counter has finished exactly `n` cells -/

/-- **At the end of the `n`-th cell of the tape every cell counter has answered `n` requests on
the `check` channel and has given `n` answers on the `sync` channel.** -/
theorem parts_full_counts (D : SolutionPlanData N w K) {n : ℕ} (hn : n ≤ (K + 1) * (K + 1))
    {p ph : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))} (hp : p <+: D.as₁)
    (hsplit : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph
      (tapePrefix Q Γ K n D.sym)) :
    ∀ l ∈ parts, l.countP (isStart SyncKind.check) = n ∧
      l.countP (isRespond SyncKind.sync) = n := by
  have hstart : p.countP (isStart SyncKind.check) = n * (K + 1) :=
    countP_isStart_eq_of_tape hp hsplit (by simp) (by simp) (by simp)
  have hsync : p.countP (isStart SyncKind.sync) = n * (K + 1) :=
    countP_isStart_eq_of_tape hp hsplit (by simp) (by simp) (by simp)
  have hpa : PartsAt parts n n := lockstep D n hn p parts ph _ hp hsplit hstart hsync
  -- the answers on the `sync` channel
  have hlen : parts.length = K + 1 := parts_length hsplit
  have hwait : p.countP (isWait SyncKind.sync) = n * (K + 1) := by
    rw [countP_isWait_eq_tape hsplit (by simp)]
    simp
  obtain ⟨r, hr⟩ := hp
  have hpq : D.as₁ ++ [TMAct.check (TMFact.st D.f)] =
      p ++ (r ++ [TMAct.check (TMFact.st D.f)]) := by
    rw [← hr]; simp
  obtain ⟨-, -, h₃, -⟩ := countP_prefix_alternates_fix SyncKind.sync D.isPlan hpq
  have hsum : p.countP (isRespond SyncKind.sync) =
      (parts.map fun l => l.countP (isRespond SyncKind.sync)).sum :=
    countP_isRespond_eq_sum hsplit (by simp)
  have hle : ∀ y ∈ parts.map fun l => l.countP (isRespond SyncKind.sync), y ≤ n := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    have := part_respond_le_start hsplit SyncKind.sync hl
    rw [(hpa l hl).2] at this
    exact this
  have hub : (parts.map fun l => l.countP (isRespond SyncKind.sync)).sum ≤ n * (K + 1) := by
    have := sum_le_mul_length hle
    simpa [hlen] using this
  have heq : (parts.map fun l => l.countP (isRespond SyncKind.sync)).sum =
      n * (parts.map fun l => l.countP (isRespond SyncKind.sync)).length := by
    simp only [List.length_map, hlen]
    omega
  intro l hl
  exact ⟨(hpa l hl).1, all_eq_of_sum_of_le hle heq _ (List.mem_map_of_mem hl)⟩

/-- **At the end of the `n`-th cell of the tape every cell counter has executed exactly the
stream of its first `n` cells.** -/
theorem parts_eq_cells (D : SolutionPlanData N w K) {n : ℕ} (hn : n ≤ (K + 1) * (K + 1))
    {p ph : List (TMAct Q Γ)} {parts : List (List (TMAct Q Γ))} (hp : p <+: D.as₁)
    (hsplit : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) p parts ph
      (tapePrefix Q Γ K n D.sym)) :
    ∀ j, ∀ hj : j < parts.length,
      parts[j] = roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j)) := by
  intro j hj
  have hlen : parts.length = K + 1 := parts_length hsplit
  have hj' : j < D.ass.length := by rw [D.card]; omega
  have hpre : parts[j] <+: D.ass[j] := hsplit.parts_prefix.get hj hj'
  rw [D.runs j hj'] at hpre
  have hjK : j < K + 1 := by omega
  obtain ⟨hcf, hcg⟩ := parts_full_counts D hn hp hsplit parts[j] (List.getElem_mem hj)
  have hdle := D.dle j hjK
  exact prefix_counterRun_eq (N := N) (w := w) (by omega) (D.decisions j hjK) hpre hn hcf hcg

/-! ### The cut -/

/-- **A solution plan, cut at the `assert` of the cell `n` of the tape.**

The plan reads `u ++ assert (sym n) :: (m ++ v)`, and the piece `m` is an interleaving of the
`n`-th cell of every one of the `K + 1` cell counters with the remaining actions of the tape's
cell `n` and with a piece of the stream of the head counter: *everything the counters do during
the cell `n` happens between the two `assert`s of the tape.* -/
theorem exists_cellCut (D : SolutionPlanData N w K) {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    ∃ (u m v Hm : List (TMAct Q Γ)) (parts : List (List (TMAct Q Γ))),
      D.as₁ = u ++ TMAct.assert (D.sym n) :: (m ++ v) ∧
        PlanInter parts Hm (cellTail Q Γ K) m ∧ Hm.Sublist (headStream Q Γ K) ∧
        parts.length = K + 1 ∧
        ∀ j, ∀ hj : j < parts.length,
          parts[j] = counterCell Q Γ K (D.d j) (D.P j) (D.cc j) n := by
  classical
  -- cut at the end of the cell `n`
  obtain ⟨pss, H₁, H₂, W₁, W₂, hass, hH, hW, hp₁, hp₂⟩ :=
    D.planInter.cut (tapeStream_split (Q := Q) (Γ := Γ) (K := K) (sym := D.sym)
      (n := n + 1) (by omega))
  -- cut the first piece at the `assert` of the cell `n`
  obtain ⟨qss, H₁₁, H₁₂, u, m, hpss, hH₁, hW₁, hq₁, hq₂⟩ :=
    hp₁.cut_at (tapePrefix_succ (Q := Q) (Γ := Γ) (K := K) (sym := D.sym) n)
  have hlenq : qss.length = pss.length := by
    have := congrArg List.length hpss
    simpa using this.symm
  have hlenp : pss.length = K + 1 := by
    have := congrArg List.length hass
    rw [D.card] at this
    simpa using this.symm
  -- the two moments
  have hu : u <+: D.as₁ := by
    refine ⟨TMAct.assert (D.sym n) :: (m ++ W₂), ?_⟩
    rw [hW, hW₁]; simp
  have hW₁pre : W₁ <+: D.as₁ := ⟨W₂, hW.symm⟩
  have hforallp : List.Forall₂ (· <+: ·) (pss.map Prod.fst) D.ass := by
    rw [hass]; exact forall₂_prefix_map_fst pss
  have hforallq : List.Forall₂ (· <+: ·) (qss.map Prod.fst) D.ass := by
    refine forall₂_prefix_trans ?_ hforallp
    rw [hpss]; exact forall₂_prefix_map_fst qss
  have hsplitp : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) W₁ (pss.map Prod.fst) H₁
      (tapePrefix Q Γ K (n + 1) D.sym) :=
    isPlanSplit_of_planInter hp₁ hforallp ⟨H₂, hH.symm⟩
      ⟨_, (tapeStream_split (Q := Q) (Γ := Γ) (K := K) (sym := D.sym) (n := n + 1)
        (by omega)).symm⟩
  have hsplitq : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) u (qss.map Prod.fst) H₁₁
      (tapePrefix Q Γ K n D.sym) := by
    refine isPlanSplit_of_planInter hq₁ hforallq ?_ ?_
    · exact (List.prefix_append H₁₁ H₁₂).trans (hH₁ ▸ ⟨H₂, hH.symm⟩)
    · exact ⟨_, (tapeStream_split (Q := Q) (Γ := Γ) (K := K) (sym := D.sym) (n := n)
        (by omega)).symm⟩
  have hcellsp := parts_eq_cells D (n := n + 1) (by omega) hW₁pre hsplitp
  have hcellsq := parts_eq_cells D (n := n) (by omega) hu hsplitq
  refine ⟨u, m, W₂, H₁₂, qss.map Prod.snd, ?_, hq₂, ?_, ?_, ?_⟩
  · rw [hW, hW₁]; simp
  · refine List.Sublist.trans ?_ (List.IsPrefix.sublist (⟨H₂, hH.symm⟩ : H₁ <+: headStream Q Γ K))
    exact hH₁ ▸ List.sublist_append_right H₁₁ H₁₂
  · simp [hlenq, hlenp]
  · intro j hj
    have hjq : j < qss.length := by simpa using hj
    have hjp : j < pss.length := by omega
    have hjK : j < K + 1 := by omega
    have hsum : (pss.map Prod.fst)[j]'(by simpa using hjp) =
        (qss.map Prod.fst)[j]'(by simpa using hjq) ++
          (qss.map Prod.snd)[j]'(by simpa using hjq) := by
      have h := congrArg (fun l => l[j]?) hpss
      simp only [List.getElem?_map] at h
      have h1 : qss[j]? = some qss[j] := List.getElem?_eq_getElem hjq
      have h2 : pss[j]? = some pss[j] := List.getElem?_eq_getElem hjp
      rw [h2, h1] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp [List.getElem_map, h]
    have e1 := hcellsq j (by simpa using hjq)
    have e2 := hcellsp j (by simpa using hjp)
    rw [roundStream_succ] at e2
    have key : roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j)) ++
        counterCell Q Γ K (D.d j) (D.P j) (D.cc j) n =
        roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j)) ++
          (qss.map Prod.snd)[j]'(by simpa using hjq) := by
      rw [← e2, hsum, e1]
    exact (List.append_cancel_left key).symm

end TMEnc

end HTN
