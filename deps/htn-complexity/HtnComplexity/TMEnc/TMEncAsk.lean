import HtnComplexity.TMEnc.TMEncPrefix
/-!
# How many synchronisation steps the tape asks for

The requests on a cell channel (`check` or `sync`) all come from the produced tape cells: the
body of `produce` is `(assert c, acquire_head, C^{K+1}_{acquire_check}, C^{K+1}_{acquire_sync})`,
so a cell asks each of the `K + 1` cell counters for one step of each of the two cell channels.

This file counts them.  The weight `HTN.TMEnc.wAsk` is balanced for both the printed and the
repaired domain, and gives

* `HTN.TMEnc.countP_call_eq_cube` / `HTN.TMEnc.countP_call_eq_cube_fix` — **every plan issues
  exactly `(K+1)³` requests on each cell channel**, one for each of the `K + 1` counters at each
  of the `(K+1)²` cells of the witness `W = #w₀#w₁…#w_K`;
* `HTN.TMEnc.countP_handshake_eq_cube_fix` — for the repaired construction the answers agree
  with the requests: all four synchronisation actions of a cell channel occur exactly `(K+1)³`
  times in a plan.  (For the printed construction they cannot, which is why it has no plan at
  all; see `HtnComplexity/TMEnc/TMEncCheck.lean`.)
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The weight -/

/-- How many requests on the cell channel `x` the full expansion of a compound task issues. -/
def askCount (x : SyncKind) (w : List Γ) (K : ℕ) : TMTask Q Γ → ℤ
  | .acquire y => if y = x then 1 else 0
  | .produce => (K : ℤ) + 1
  | .produceSym _ => (K : ℤ) + 1
  | .tapeProduce => ((K : ℤ) + 1) * ((K : ℤ) + 1)
  | .produceInit => ((K : ℤ) + 1) * ((1 + max w.length 1 + (K - w.length) : ℕ) : ℤ)
  | .produceWord i => ((K : ℤ) + 1) * ((max (w.length - i) 1 : ℕ) : ℤ)
  | .cSeq t k => (k : ℤ) * askCount x w K t
  | .cPar t k => (k : ℤ) * askCount x w K t
  | .sI => ((K : ℤ) + 1) * (((1 + max w.length 1 + (K - w.length)) + K * (1 + K) : ℕ) : ℤ)
  | _ => 0

/-- The weight counting the requests on a cell channel. -/
def wAsk (x : SyncKind) (w : List Γ) (K : ℕ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => if isCall x a then 1 else 0
  | Sum.inr t => askCount x w K t

lemma sum_wAsk_bodies (x : SyncKind) (hx : x = SyncKind.check ∨ x = SyncKind.sync)
    {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodies N w K t) :
    (ls.flatten.map (wAsk x w K)).sum = wAsk x w K (Sum.inr t) := by
  rcases hx with rfl | rfl
  all_goals
  cases t with
  | acquire y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      cases y <;> simp [wAsk, askCount, isCall]
  | release y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      cases y <;> simp [wAsk, askCount, isCall]
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wAsk, askCount, isCall]
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAsk, askCount, isCall]
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [wAsk, askCount, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAsk, askCount]
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAsk, askCount]
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wAsk, askCount, isCall]
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAsk, askCount, isCall]
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAsk, askCount, isCall]
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAsk, askCount]
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
      simp [wAsk, askCount, isCall, List.map_replicate, List.sum_replicate]
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> simp [wAsk, askCount, isCall]
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wAsk, askCount]
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [wAsk, askCount, Nat.sub_zero, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      push_cast
      ring
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls with hlt
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : 1 + max (w.length - (i + 1)) 1 = max (w.length - i) 1 := by omega
        simp only [wAsk, askCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have hcast : ((max (w.length - i) 1 : ℕ) : ℤ) =
            1 + ((max (w.length - (i + 1)) 1 : ℕ) : ℤ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk.symm
        rw [hcast]
        ring
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : (1 : ℕ) = max (w.length - i) 1 := by omega
        simp only [wAsk, askCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have hcast : ((max (w.length - i) 1 : ℕ) : ℤ) = 1 := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk.symm
        rw [hcast]
        ring
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      simp [wAsk, askCount, isCall]
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wAsk, askCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wAsk, askCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [wAsk, askCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have hhalf : ((k / 2 : ℕ) : ℤ) * 2 = (k : ℤ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (by omega : k / 2 * 2 = k)
        rw [← hhalf]
        ring
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [wAsk, askCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have hk1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
          have : 1 ≤ k := by omega
          push_cast [this]
          ring
        rw [hk1]
        ring
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wAsk, askCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wAsk, askCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [wAsk, askCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        have hhalf : ((k / 2 : ℕ) : ℤ) * 2 = (k : ℤ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (by omega : k / 2 * 2 = k)
        rw [← hhalf]
        ring
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [wAsk, askCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        have hk1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
          have : 1 ≤ k := by omega
          push_cast [this]
          ring
        rw [hk1]
        ring
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

lemma sum_wAsk_bodiesFix (x : SyncKind) (hx : x = SyncKind.check ∨ x = SyncKind.sync)
    {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) :
    (ls.flatten.map (wAsk x w K)).sum = wAsk x w K (Sum.inr t) := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    simp [checkerBodyFix, wAsk, askCount]
  · rw [bodiesFix_eq_of_ne ht1] at hls
    exact sum_wAsk_bodies x hx hls

private lemma sum_wAsk_initChainsFix (x : SyncKind) :
    (((initChainsFix K : List (List (TMAct Q Γ ⊕ TMTask Q Γ))) ++
      [[Sum.inr (TMTask.done : TMTask Q Γ)]]).flatten.map (wAsk x w K)).sum =
      wAsk x w K (Sum.inr (TMTask.sI : TMTask Q Γ)) := by
  simp only [initChainsFix, headChainFix, wAsk, askCount, List.flatten_cons,
    List.flatten_nil, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.append_nil]
  push_cast
  ring

private lemma sum_wAsk_initChains (x : SyncKind) :
    (((initChains K : List (List (TMAct Q Γ ⊕ TMTask Q Γ))) ++
      [[Sum.inr (TMTask.done : TMTask Q Γ)]]).flatten.map (wAsk x w K)).sum =
      wAsk x w K (Sum.inr (TMTask.sI : TMTask Q Γ)) := by
  simp only [initChains, wAsk, askCount, isCall, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.append_nil]
  push_cast
  ring

lemma balanced_wAsk (x : SyncKind) (hx : x = SyncKind.check ∨ x = SyncKind.sync) :
    Balanced (methods N w K) (wAsk (Q := Q) (Γ := Γ) x w K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wAsk_bodies x hx hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNet K) = _
    rw [initNet, weight_gridTail]
    exact sum_wAsk_initChains x

lemma balanced_wAskFix (x : SyncKind) (hx : x = SyncKind.check ∨ x = SyncKind.sync) :
    Balanced (methodsFix N w K) (wAsk (Q := Q) (Γ := Γ) x w K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wAsk_bodiesFix x hx hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail]
    exact sum_wAsk_initChainsFix x

lemma sum_map_wAsk (x : SyncKind) (as : List (TMAct Q Γ)) :
    (as.map fun a => wAsk (Q := Q) (Γ := Γ) x w K (Sum.inl a)).sum =
      (as.countP (isCall x) : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : isCall x a = true
      · simp [wAsk, h]; ring
      · simp [wAsk, h]

/-! ### The number of requests -/

private lemma cube_of_le (hw0 : w ≠ []) (hwK : w.length ≤ K) :
    ((K : ℤ) + 1) * (((1 + max w.length 1 + (K - w.length)) + K * (1 + K) : ℕ) : ℤ) =
      (((K + 1) ^ 3 : ℕ) : ℤ) := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw0
  have hA : (1 + max w.length 1 + (K - w.length)) + K * (1 + K) = (K + 1) ^ 2 := by
    have hmax : max w.length 1 = w.length := by omega
    rw [hmax]
    ring_nf
    omega
  rw [hA]
  push_cast
  ring

/-- **Every plan of the encoded problem issues exactly `(K+1)³` requests on each cell
channel**: one for each of the `K + 1` cell counters at each of the `(K+1)²` cells of the
witness. -/
theorem countP_call_eq_cube (x : SyncKind) (hx : x = SyncKind.check ∨ x = SyncKind.sync)
    (hw0 : w ≠ []) (hwK : w.length ≤ K) {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    as.countP (isCall x) = (K + 1) ^ 3 := by
  have hw := weight_of_netYield (balanced_wAsk (N := N) (w := w) (K := K) x hx) h
  rw [sum_map_wAsk, weight_tnI] at hw
  simp only [wAsk, askCount] at hw
  rw [cube_of_le hw0 hwK] at hw
  exact_mod_cast hw

/-- The same count for the repaired construction. -/
theorem countP_call_eq_cube_fix (x : SyncKind) (hx : x = SyncKind.check ∨ x = SyncKind.sync)
    (hw0 : w ≠ []) (hwK : w.length ≤ K) {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isCall x) = (K + 1) ^ 3 := by
  have hw := weight_of_netYield (balanced_wAskFix (N := N) (w := w) (K := K) x hx) h
  rw [sum_map_wAsk, weight_tnIFix] at hw
  simp only [wAsk, askCount] at hw
  rw [cube_of_le hw0 hwK] at hw
  exact_mod_cast hw

/-- **The complete handshake count of the repaired construction.**  In every plan of the
repaired problem each of the four synchronisation actions of each cell channel occurs exactly
`(K+1)³` times: the `(K+1)²` cells of the witness each ask the `K + 1` cell counters once, and
each request is answered. -/
theorem countP_handshake_eq_cube_fix (x : SyncKind)
    (hx : x = SyncKind.check ∨ x = SyncKind.sync) (hw0 : w ≠ []) (hwK : w.length ≤ K)
    {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isCall x) = (K + 1) ^ 3 ∧ as.countP (isWait x) = (K + 1) ^ 3 ∧
      as.countP (isStart x) = (K + 1) ^ 3 ∧ as.countP (isRespond x) = (K + 1) ^ 3 := by
  have hxh : x ≠ SyncKind.head := by rcases hx with rfl | rfl <;> simp
  have hcall := countP_call_eq_cube_fix x hx hw0 hwK h
  have hwait := countP_call_eq_countP_wait_fix (N := N) (w := w) (K := K) x h
  have hstart := countP_start_eq_countP_call_fix x hx hw0 hwK h
  have hresp := countP_respond_eq_countP_start_fix (N := N) (w := w) (K := K) x h
  exact ⟨hcall, by omega, by omega, by omega⟩

end TMEnc

end HTN
