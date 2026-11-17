import FondHtn.HardMP.Sem
/-!
# Correctness of the reductions

Both descriptions `FOND.HardMP.descA` and `FOND.HardMP.descR` are strongly solvable with
method-based policies iff the dynamic program of Thm. 4.2.1 accepts the source description.
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn

/-! ## The initial program -/

theorem mem_wpI_goal {p : ProbDesc} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI (goalI p) Ψ ↔ goalB p (sv (pfacts p) (vecC (pfacts p).length c 1)) = true ∧ c ∈ Ψ := by
  have hV : (pfacts p).Nodup := List.nodup_dedup _
  unfold goalI goalB
  cases hall : p.goalPos.all (fun f => decide (f ∈ pfacts p))
  · have : ¬ ∀ f ∈ p.goalPos, f ∈ pfacts p := by simpa using hall
    simp only [cond_false, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not]
    refine ⟨fun h => by simp [wpI] at h, fun ⟨⟨h1, _⟩, _⟩ => absurd (fun f hf => sv_sub (h1 f hf)) this⟩
  · have h0 : ∀ f ∈ p.goalPos, f ∈ pfacts p := by simpa using hall
    simp only [cond_true, mem_wpI_chk, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
      Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      forall_exists_index, and_imp]
    refine and_congr_left fun _ => ⟨fun ⟨h1, h2⟩ => ⟨fun f hf => ?_, fun f hf hm => ?_⟩,
      fun ⟨h1, h2⟩ => ⟨fun x j hj hm he => ?_, fun x j hj hm he => ?_⟩⟩
    · have hj := List.idxOf_lt_length_of_mem (h0 f hf)
      refine (mem_sv_vecC' hV).2 ⟨h0 f hf, h1 _ _ hj ?_ rfl⟩
      rwa [getI_of_lt hj, List.getElem_idxOf]
    · obtain ⟨hfV, hc⟩ := (mem_sv_vecC' hV).1 hm
      have hj := List.idxOf_lt_length_of_mem hfV
      rw [h2 _ _ hj (by rwa [getI_of_lt hj, List.getElem_idxOf]) rfl] at hc
      exact Bool.false_ne_true hc
    · subst he; exact (mem_sv_vecC hV hj).1 (h1 _ hm)
    · subst he
      have := h2 _ hm
      rw [mem_sv_vecC hV hj] at this
      simpa using this

/-- The fields of the end vector. -/
def eFields (n : ℕ) : List ℕ := (List.range n).map (fSlot 1)

theorem mem_wpP_init {p : ProbDesc} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpP (progInit p) Ψ ↔ ∃ g, goalB p (sv (pfacts p)
      (vecC (pfacts p).length (c.sets (eFields (pfacts p).length) g) 1)) = true ∧
        c.sets (eFields (pfacts p).length) g ∈ Ψ := by
  unfold progInit
  rw [wpP_append, mem_wpP_guess ((List.nodup_range).map fun a b h => (fSlot_inj.1 h).2)]
  simp only [wpP_cons, wpP_nil, mem_wpI_goal]
  rfl

theorem sets_eFields_val_ne {n : ℕ} {c : Cfg} {g : ℕ → Bool} {x : ℕ} (hx : ∀ j, x ≠ fSlot 1 j) :
    (c.sets (eFields n) g).val x = c.val x := by
  rw [Cfg.sets_val, if_neg]
  simp only [eFields, List.mem_map, List.mem_range, not_exists, not_and]
  exact fun j _ he => hx j he.symm

theorem vecC_cfgInit (p : ProbDesc) :
    vecC (pfacts p).length (cfgInit p) 0 = vecOf (pfacts p) p.init := by
  have hV : (pfacts p).Nodup := List.nodup_dedup _
  apply List.ext_getElem (by simp [vecOf])
  intro j h1 h2
  simp only [getElem_vecC, vecOf, List.getElem_map, cfgInit, fSlot_inj, true_and]
  have hj : j < (pfacts p).length := by simpa using h1
  congr 1
  apply propext
  constructor
  · rintro ⟨j', hj', rfl, hm⟩; rwa [getI_of_lt hj'] at hm
  · intro hm; exact ⟨j, hj, rfl, by rwa [getI_of_lt hj]⟩

theorem enc_cfgInit (p : ProbDesc) : {f | f ∈ initFacts p} = (cfgInit p).enc := by
  ext y
  simp only [initFacts, Set.mem_setOf_eq, List.mem_cons, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  rcases fact_or_curF y with ⟨f, rfl⟩ | ⟨x, rfl⟩
  · rw [Cfg.fact_mem_enc]
    simp only [cfgInit, decide_eq_true_eq, fact_eq_fact]
    constructor
    · rintro (h | ⟨j, ⟨hj, hm⟩, rfl⟩)
      · exact absurd h (fact_ne_curF _ _)
      · exact ⟨j, hj, rfl, hm⟩
    · rintro ⟨j, hj, rfl, hm⟩
      exact Or.inr ⟨j, ⟨hj, hm⟩, rfl⟩
  · rw [Cfg.curF_mem_enc]
    simp only [cfgInit]
    constructor
    · rintro (h | ⟨j, -, h⟩)
      · exact (curF_inj h).symm
      · exact absurd h (fact_ne_curF _ _)
    · intro h; exact Or.inl (by rw [h])

/-! ## Rounds in the list game -/

/-- A bound on the length of the programs of a round. -/
def Lr (p : ProbDesc) : ℕ := ((rules p).map List.length).sum

theorem length_le_Lr {p : ProbDesc} {r : List (List ASpec)} (hr : r ∈ rules p) :
    r.length ≤ Lr p :=
  List.le_sum_of_mem (List.mem_map.2 ⟨r, hr, rfl⟩)

section Round

variable {p : ProbDesc} {ex : List (Bool × ℕ)} {D : FProbDesc} {O : List MethodDesc}
  {extra : List (List (Bool × ℕ))}
  (hv : D.Valid) (hA : D.actions = acts (prgs p)) (hM : D.methods = chainMeths (prgs p) ex ++ O)
  (hO : ∀ e ∈ O, ∀ r pc, e.1 ≠ cN r pc) (hmeth : ∀ e ∈ D.methods, ∃ c ls, e = meth c ls)
  (hspec : ∀ r < (prgs p).length, ∀ pc < ((prgs p).getI r).length,
    ∀ alt < (((prgs p).getI r).getI pc).length, ((((prgs p).getI r).getI pc).getI alt).WF)
  (hR : ∀ ls, meth roundN ls ∈ D.methods ↔
    (∃ r < (rules p).length, ls = [(true, cN (r + 1) 0)]) ∨ ls ∈ extra)
include hv hA hM hO hmeth hspec hR

theorem round_sound_L {n : ℕ} {xs : List (ℕ ⊕ ℕ)} {c : Cfg} {Φ : Set (Set ℕ)}
    (h : D.toProblem.LRunH (n + 1) (Sum.inr roundN :: xs) c.enc Φ) :
    (∃ r ∈ rules p, c ∈ wpP r {c' | D.toProblem.LRunH n (ex.map toLab ++ xs) c'.enc Φ}) ∨
      ∃ b ∈ extra, D.toProblem.LRunH n (b.map toLab ++ xs) c.enc Φ := by
  obtain ⟨bs, hb, h⟩ := Problem.lrunH_comp_iff.1 h
  obtain ⟨ls, hls, rfl⟩ := (seqBodyF_iff hmeth).1 hb
  rcases (hR ls).1 hls with ⟨r, hr, rfl⟩ | hx
  · left
    have hr' : r + 1 < (prgs p).length := by simp [prgs]; omega
    have := chain_sound hv hA hM hO hmeth hspec hr' _ 0 (Nat.zero_add _).symm
      (by simpa [toLab] using h)
    simp only [List.drop_zero, prgs, List.getI_cons_succ] at this
    exact ⟨_, getI_memS hr, this⟩
  · exact Or.inr ⟨ls, hx, h⟩

theorem round_complete_L {m : ℕ} {xs : List (ℕ ⊕ ℕ)} {c : Cfg} {Φ : Set (Set ℕ)}
    {r : List (List ASpec)} (hr : r ∈ rules p)
    (h : c ∈ wpP r {c' | D.toProblem.LRunH m (ex.map toLab ++ xs) c'.enc Φ}) :
    D.toProblem.LRunH (m + 2 * Lr p + 2) (Sum.inr roundN :: xs) c.enc Φ := by
  obtain ⟨i, hi, rfl⟩ := exists_getI_of_mem hr
  have hi' : i + 1 < (prgs p).length := by simp [prgs]; omega
  have hc := chain_complete hv hA hM hO hmeth hspec hi' _ 0 (Nat.zero_add _).symm
    (xs := xs) (m := m) (c := c) (Φ := Φ) (by simpa [prgs] using h)
  refine Problem.LRunH.mono (.comp ((seqBodyF_iff hmeth).2 ⟨_, (hR _).2 (Or.inl ⟨i, hi, rfl⟩),
    rfl⟩) (by simpa [toLab] using hc)) ?_ le_rfl
  have := length_le_Lr hr
  simp only [prgs, List.getI_cons_succ]
  omega

end Round

theorem round_complete' {p : ProbDesc} {allV : List (List Bool)}
    (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length) {m : ℕ} {c : Cfg}
    (hc : GoodK p allV m c) : ∃ r ∈ rules p, c ∈ wpP r {c' | GoodK p allV (m - 1) c'} := by
  rcases m with _ | m
  · have hd := goodK_zero hc
    refine ⟨progNoop, by simp [rules], ?_⟩
    simp only [progNoop, wpP_cons, wpP_nil, mem_wpI_chk, List.mem_singleton, forall_eq,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨hd, Or.inl hd⟩
  · exact round_complete hall hc

/-! ## The acyclic construction: the clock -/

section Clock

variable {p : ProbDesc} {D : FProbDesc} {O : List MethodDesc} {N : ℕ}
  (hv : D.Valid) (hA : D.actions = acts (prgs p)) (hM : D.methods = chainMeths (prgs p) [] ++ O)
  (hO : ∀ e ∈ O, ∀ r pc, e.1 ≠ cN r pc) (hmeth : ∀ e ∈ D.methods, ∃ c ls, e = meth c ls)
  (hspec : ∀ r < (prgs p).length, ∀ pc < ((prgs p).getI r).length,
    ∀ alt < (((prgs p).getI r).getI pc).length, ((((prgs p).getI r).getI pc).getI alt).WF)
  (hR : ∀ ls, meth roundN ls ∈ D.methods ↔ ∃ r < (rules p).length, ls = [(true, cN (r + 1) 0)])
  (hC : ∀ j ls, meth (clkN j) ls ∈ D.methods ↔ (j = 0 ∧ ls = [(true, roundN)]) ∨
    ∃ j' < N, j = j' + 1 ∧ ls = [(true, clkN j'), (true, clkN j')])
  {allV : List (List Bool)} (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length)
include hv hA hM hO hmeth hspec hR hC hall

omit hv hA hM hO hmeth hspec hC hall in
theorem hR' : ∀ ls, meth roundN ls ∈ D.methods ↔
    (∃ r < (rules p).length, ls = [(true, cN (r + 1) 0)]) ∨ ls ∈ ([] : List (List (Bool × ℕ))) :=
  fun ls => by simp [hR]

/-- **Soundness of the clock**: the invariant propagates backwards through `clk j`. -/
theorem clk_sound : ∀ j ≤ N, ∀ {n : ℕ} {xs : List (ℕ ⊕ ℕ)} {Φ : Set (Set ℕ)} {c : Cfg},
    D.toProblem.LRunH n (Sum.inr (clkN j) :: xs) c.enc Φ →
    (∀ m c', D.toProblem.LRunH m xs c'.enc Φ → Good p allV c') → Good p allV c := by
  intro j
  induction j with
  | zero =>
    intro _ n xs Φ c h hxs
    rcases n with _ | n
    · exact absurd h Problem.not_lrunH_zero_cons
    obtain ⟨bs, hb, h⟩ := Problem.lrunH_comp_iff.1 h
    obtain ⟨ls, hls, rfl⟩ := (seqBodyF_iff hmeth).1 hb
    rcases (hC 0 ls).1 hls with ⟨-, rfl⟩ | ⟨j', -, hj, -⟩
    · simp only [List.map_cons, List.map_nil, toLab, if_true, List.cons_append,
        List.nil_append] at h
      rcases n with _ | n
      · exact absurd h Problem.not_lrunH_zero_cons
      rcases round_sound_L hv hA hM hO hmeth hspec (hR' hR) h with
        ⟨r, hr, hc⟩ | ⟨b, hb, -⟩
      · exact round_sound hall (fun c' hc' => hxs _ c' (by simpa using hc')) hr hc
      · simp at hb
    · omega
  | succ j ih =>
    intro hj n xs Φ c h hxs
    rcases n with _ | n
    · exact absurd h Problem.not_lrunH_zero_cons
    obtain ⟨bs, hb, h'⟩ := Problem.lrunH_comp_iff.1 h
    obtain ⟨ls, hls, rfl⟩ := (seqBodyF_iff hmeth).1 hb
    rcases (hC (j + 1) ls).1 hls with ⟨h0, -⟩ | ⟨j', -, hj', rfl⟩
    · omega
    · obtain rfl : j' = j := by omega
      exact ih (by omega) (by simpa [toLab] using h') fun m c' hc' => ih (by omega) hc' hxs

/-- **Completeness of the clock.** -/
theorem clk_complete : ∀ j ≤ N, ∀ {h₀ m : ℕ} {xs : List (ℕ ⊕ ℕ)} {Φ : Set (Set ℕ)} {c : Cfg},
    (∀ c', GoodK p allV (m - 2 ^ j) c' → D.toProblem.LRunH h₀ xs c'.enc Φ) →
    GoodK p allV m c →
    D.toProblem.LRunH (h₀ + (2 ^ (j + 1) - 1) * (2 * Lr p + 4)) (Sum.inr (clkN j) :: xs) c.enc Φ := by
  intro j
  induction j with
  | zero =>
    intro _ h₀ m xs Φ c hxs hc
    obtain ⟨r, hr, hc⟩ := round_complete' hall hc
    have hround := round_complete_L hv hA hM hO hmeth hspec (hR' hR)
      (ex := []) (xs := xs) (m := h₀) (Φ := Φ) hr
      (wpP_mono _ (fun c' hc' => hxs c' (by simpa using hc')) hc)
    refine Problem.LRunH.mono (.comp ((seqBodyF_iff hmeth).2 ⟨[(true, roundN)],
      (hC 0 _).2 (Or.inl ⟨rfl, rfl⟩), rfl⟩) (by simpa [toLab] using hround)) ?_ le_rfl
    simp
    omega
  | succ j ih =>
    intro hj h₀ m xs Φ c hxs hc
    have hin := ih (by omega) (h₀ := h₀ + (2 ^ (j + 1) - 1) * (2 * Lr p + 4))
      (xs := Sum.inr (clkN j) :: xs) (m := m) (Φ := Φ) (c := c)
      (fun c' hc' => ih (by omega) (m := m - 2 ^ j) (fun c'' hc'' => hxs c'' (by
        rw [Nat.sub_sub, ← two_mul, ← pow_succ'] at hc''; exact hc'')) hc') hc
    refine Problem.LRunH.mono (.comp ((seqBodyF_iff hmeth).2 ⟨[(true, clkN j), (true, clkN j)],
      (hC (j + 1) _).2 (Or.inr ⟨j, by omega, rfl, rfl⟩), rfl⟩)
      (by simpa [toLab] using hin)) ?_ le_rfl
    have h1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    rw [pow_succ 2 (j + 1)]
    have : (2 ^ (j + 1) * 2 - 1) * (2 * Lr p + 4) =
        2 * ((2 ^ (j + 1) - 1) * (2 * Lr p + 4)) + (2 * Lr p + 4) := by
      zify [h1, show 1 ≤ 2 ^ (j + 1) * 2 by omega]; ring
    rw [this]; omega

end Clock

/-! ## The regular construction: the loop -/

section Loop

variable {p : ProbDesc} {D : FProbDesc} {O : List MethodDesc}
  (hv : D.Valid) (hA : D.actions = acts (prgs p))
  (hM : D.methods = chainMeths (prgs p) [(true, roundN)] ++ O)
  (hO : ∀ e ∈ O, ∀ r pc, e.1 ≠ cN r pc) (hmeth : ∀ e ∈ D.methods, ∃ c ls, e = meth c ls)
  (hspec : ∀ r < (prgs p).length, ∀ pc < ((prgs p).getI r).length,
    ∀ alt < (((prgs p).getI r).getI pc).length, ((((prgs p).getI r).getI pc).getI alt).WF)
  (hR : ∀ ls, meth roundN ls ∈ D.methods ↔
    (∃ r < (rules p).length, ls = [(true, cN (r + 1) 0)]) ∨ ls ∈ [[(false, finN)]])
  {allV : List (List Bool)} (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length)
include hv hA hM hO hmeth hspec hR hall

/-- **Soundness of the loop.** -/
theorem loop_sound : ∀ n {c : Cfg},
    D.toProblem.LRunH n [Sum.inr roundN] c.enc Set.univ → Good p allV c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c h
    rcases n with _ | n
    · exact absurd h Problem.not_lrunH_zero_cons
    rcases round_sound_L hv hA hM hO hmeth hspec hR h with ⟨r, hr, hc⟩ | ⟨b, hb, h⟩
    · exact round_sound hall (fun c' hc' => ih n (by omega) (by simpa [toLab] using hc')) hr hc
    · simp only [List.mem_singleton] at hb
      subst hb
      rcases n with _ | n
      · exact absurd h Problem.not_lrunH_zero_cons
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
        List.cons_append, List.nil_append] at h
      exact Or.inl ((lrunH_finN hv hA).1 h).1

/-- **Completeness of the loop.** -/
theorem loop_complete : ∀ m {c : Cfg}, GoodK p allV m c →
    D.toProblem.LRunH ((m + 1) * (2 * Lr p + 2)) [Sum.inr roundN] c.enc Set.univ := by
  intro m
  induction m with
  | zero =>
    intro c hc
    have hd := goodK_zero hc
    have h2 : D.toProblem.LRunH 2 [Sum.inr roundN] c.enc Set.univ := by
      refine .comp ((seqBodyF_iff hmeth).2 ⟨[(false, finN)], (hR _).2 (Or.inr (by simp)), rfl⟩) ?_
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
        List.cons_append, List.nil_append]
      exact (lrunH_finN hv hA).2 ⟨hd, .nil trivial⟩
    exact h2.mono (by nlinarith) le_rfl
  | succ m ih =>
    intro c hc
    obtain ⟨r, hr, hc⟩ := round_complete hall hc
    have := round_complete_L hv hA hM hO hmeth hspec hR (xs := []) hr
      (wpP_mono _ (fun c' hc' => by simpa [toLab] using ih hc') hc)
    refine this.mono ?_ le_rfl
    ring_nf; omega

end Loop

end HardMP

end FOND
