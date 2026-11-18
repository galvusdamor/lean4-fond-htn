import ComplexityTheory.TOtoHD.Amp.Run
/-!
# The amplifier: the run of a multiplication loop

`loop_run`: with the two pairs of level `k` at rest (`B k` tokens on each `false` side) and a
budget of `2 B k + 2` tests and `2 B k (2 B k + 2)` moves of level `k`, the multiplication loop
over the counters of level `k` at site `s` produces `B k * B k` tokens on `tgt k s` and ends at
`after k s` with the pairs at rest again.
-/

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

/-- Pointwise proof of an equality of explicit markings, with products normalised. -/
macro "mk_eq'" : tactic => `(tactic| (
  funext p
  simp only [mv, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, δ_apply, smul_eq_mul,
    List.count_cons, List.count_nil, beq_iff_eq, Nat.add_mul, Nat.mul_add, Nat.mul_one,
    Nat.one_mul]
  rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;> simp <;>
    split_ifs <;> first | omega | ring | (ring_nf; omega)))

theorem mv_nn (m : Mk) : mv m [] [] = m := by funext p; simp [mv]

section loop

variable {P : CM Q Φ} {L : ℕ} {S : Finset Φ} {k : ℕ} {s : Site}

theorem inner_loop (hk : k < L) (n : ℕ) : ∀ j ≤ n,
    Reach P L (.sp k s .inner, S, n • δ (.side k true false))
      (.sp k s .inner, S, (n - j) • δ (.side k true false) + j • δ (.side k true true) +
        j • δ (tgt k s)) := by
  intro j
  induction j with
  | zero => intro _; apply reach_of_eq; simp
  | succ j ih =>
    intro hj
    refine (ih (by omega)).tail (astep0 (IsRule.inner k s hk) ?_ ?_)
    · intro p
      rcases s with r0 | b0 <;> (try cases r0) <;> (try cases b0) <;> (try simp only [tgt]) <;>
        (rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;> simp <;>
          split_ifs <;> omega)
    · rcases s with r0 | b0 <;> (try cases r0) <;> (try cases b0) <;> (try simp only [tgt]) <;> mk_eq

theorem restj_loop (hk : k < L) (n : ℕ) : ∀ j ≤ n,
    Reach P L (.sp k s .restj, S, n • δ (.side k true true))
      (.sp k s .restj, S, (n - j) • δ (.side k true true) + j • δ (.side k true false)) := by
  intro j
  induction j with
  | zero => intro _; apply reach_of_eq; simp
  | succ j ih =>
    intro hj
    refine (ih (by omega)).tail (astep0 (IsRule.restj k s hk) ?_ ?_)
    · intro p
      rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;> simp <;>
        split_ifs <;> omega
    · mk_eq

theorem resti_loop (hk : k < L) (n : ℕ) : ∀ j ≤ n,
    Reach P L (.sp k s .resti, S, n • δ (.side k false true))
      (.sp k s .resti, S, (n - j) • δ (.side k false true) + j • δ (.side k false false)) := by
  intro j
  induction j with
  | zero => intro _; apply reach_of_eq; simp
  | succ j ih =>
    intro hj
    refine (ih (by omega)).tail (astep0 (IsRule.resti k s hk) ?_ ?_)
    · intro p
      rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;> simp <;>
        split_ifs <;> omega
    · mk_eq

/-- The rest of an outer iteration, after the inner loop. -/
theorem iter_rest (hk : k < L) (n : ℕ) :
    Reach P L (.sp k s .inner, S, n • δ (.side k true true) + 2 • δ (.d k) +
        (4 * n) • δ (.c k) + δ (.side k false false))
      (.sp k s .outer, S, n • δ (.side k true false) + δ (.side k false true)) := by
  -- the test of the `false` side of the inner counter
  have h1 := astep0 (S := S) (IsRule.innerZ (P := P) k s hk)
    (m := n • δ (.side k true true) + 2 • δ (.d k) + (4 * n) • δ (.c k) +
      δ (.side k false false))
    (m' := n • δ (.side k true true) + δ (.d k) + (4 * n) • δ (.c k) +
      δ (.side k false false))
    (by intro p; rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;>
      simp <;> split_ifs <;> omega)
    (by mk_eq)
  have h2 := reach_frame (test_run (P := P) (L := L) (S := S) (.sj k s false) k true false rfl
      rfl rfl n) (m0 := δ (.d k) + (2 * n) • δ (.c k) + δ (.side k false false))
    (m := n • δ (.side k true true) + δ (.d k) + (4 * n) • δ (.c k) +
      δ (.side k false false))
    (m' := n • δ (.side k true true) + δ (.d k) + (2 * n) • δ (.c k) +
      δ (.side k false false))
    (by mk_eq) (by mk_eq)
  have h3 := astep0 (S := S) (IsRule.sjF (P := P) k s hk)
    (m := n • δ (.side k true true) + δ (.d k) + (2 * n) • δ (.c k) +
      δ (.side k false false))
    (m' := n • δ (.side k true true) + δ (.d k) + (2 * n) • δ (.c k) +
      δ (.side k false false))
    (fun p => by simp) (by mk_eq)
  have h4 := reach_frame (restj_loop (P := P) (S := S) (s := s) hk n n le_rfl)
    (m0 := δ (.d k) + (2 * n) • δ (.c k) + δ (.side k false false))
    (m := n • δ (.side k true true) + δ (.d k) + (2 * n) • δ (.c k) +
      δ (.side k false false))
    (m' := n • δ (.side k true false) + δ (.d k) + (2 * n) • δ (.c k) +
      δ (.side k false false))
    (by mk_eq) (by mk_eq)
  have h5 := astep0 (S := S) (IsRule.restjZ (P := P) k s hk)
    (m := n • δ (.side k true false) + δ (.d k) + (2 * n) • δ (.c k) +
      δ (.side k false false))
    (m' := n • δ (.side k true false) + (2 * n) • δ (.c k) + δ (.side k false false))
    (by intro p; rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;>
      simp <;> split_ifs <;> omega)
    (by mk_eq)
  have h6 := reach_frame (test_run (P := P) (L := L) (S := S) (.sj k s true) k true true rfl
      rfl rfl n) (m0 := δ (.side k false false))
    (m := n • δ (.side k true false) + (2 * n) • δ (.c k) + δ (.side k false false))
    (m' := n • δ (.side k true false) + δ (.side k false false))
    (by mk_eq) (by mk_eq)
  have h7 := astep0 (S := S) (IsRule.sjT (P := P) k s hk)
    (m := n • δ (.side k true false) + δ (.side k false false))
    (m' := n • δ (.side k true false) + δ (.side k false true))
    (by intro p; rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;>
      simp <;> split_ifs <;> omega)
    (by mk_eq)
  exact (((((h2.head h1).tail h3).trans h4).tail h5).trans h6).tail h7

/-- One outer iteration. -/
theorem iter_run (hk : k < L) (n : ℕ) :
    Reach P L (.sp k s .inner, S, n • δ (.side k true false) + 2 • δ (.d k) +
        (4 * n) • δ (.c k) + δ (.side k false false))
      (.sp k s .outer, S, n • δ (.side k true false) + δ (.side k false true) +
        n • δ (tgt k s)) := by
  have h1 := reach_frame (inner_loop (P := P) (S := S) (s := s) hk n n le_rfl)
    (m0 := 2 • δ (.d k) + (4 * n) • δ (.c k) + δ (.side k false false))
    (m := n • δ (.side k true false) + 2 • δ (.d k) + (4 * n) • δ (.c k) +
      δ (.side k false false))
    (m' := n • δ (.side k true true) + 2 • δ (.d k) + (4 * n) • δ (.c k) +
      δ (.side k false false) + n • δ (tgt k s))
    (by rcases s with r0 | b0 <;> (try cases r0) <;> (try cases b0) <;> (try simp only [tgt]) <;> mk_eq)
    (by rcases s with r0 | b0 <;> (try cases r0) <;> (try cases b0) <;> (try simp only [tgt]) <;> mk_eq)
  have h2 := reach_add (iter_rest (P := P) (S := S) (s := s) hk n) (n • δ (tgt k s))
  exact h1.trans h2

/-- The outer iterations after the first. -/
theorem outer_iter (hk : k < L) (n : ℕ) : ∀ a u : ℕ,
    Reach P L (.sp k s .outer, S, n • δ (.side k true false) + a • δ (.side k false false) +
        u • δ (.side k false true) + (2 * a) • δ (.d k) + (4 * n * a) • δ (.c k) +
        (u * n) • δ (tgt k s))
      (.sp k s .outer, S, n • δ (.side k true false) + (u + a) • δ (.side k false true) +
        ((u + a) * n) • δ (tgt k s)) := by
  intro a
  induction a with
  | zero => intro u; apply reach_of_eq; congr 2; simp
  | succ a ih =>
    intro u
    have h0 := astep0 (S := S) (IsRule.outerIn (P := P) k s hk)
      (m := n • δ (.side k true false) + (a + 1) • δ (.side k false false) +
        u • δ (.side k false true) + (2 * (a + 1)) • δ (.d k) + (4 * n * (a + 1)) • δ (.c k) +
        (u * n) • δ (tgt k s))
      (m' := n • δ (.side k true false) + (a + 1) • δ (.side k false false) +
        u • δ (.side k false true) + (2 * (a + 1)) • δ (.d k) + (4 * n * (a + 1)) • δ (.c k) +
        (u * n) • δ (tgt k s))
      (fun p => by simp) (mv_nn _)
    have h1 := reach_frame (iter_run (P := P) (S := S) (s := s) hk n)
      (m0 := a • δ (.side k false false) + u • δ (.side k false true) + (2 * a) • δ (.d k) +
        (4 * n * a) • δ (.c k) + (u * n) • δ (tgt k s))
      (m := n • δ (.side k true false) + (a + 1) • δ (.side k false false) +
        u • δ (.side k false true) + (2 * (a + 1)) • δ (.d k) + (4 * n * (a + 1)) • δ (.c k) +
        (u * n) • δ (tgt k s))
      (m' := n • δ (.side k true false) + a • δ (.side k false false) +
        (u + 1) • δ (.side k false true) + (2 * a) • δ (.d k) + (4 * n * a) • δ (.c k) +
        ((u + 1) * n) • δ (tgt k s))
      (by rcases s with r0 | b0 <;> (try cases r0) <;> (try cases b0) <;> (try simp only [tgt]) <;>
        mk_eq')
      (by rcases s with r0 | b0 <;> (try cases r0) <;> (try cases b0) <;> (try simp only [tgt]) <;>
        mk_eq')
    have h2 := ih (u + 1)
    rw [show u + 1 + a = u + (a + 1) by omega] at h2
    exact (h1.head h0).trans h2

/-- The end of the loop: the outer counter is tested full, reset, and tested empty. -/
theorem final_run (hk : k < L) (n : ℕ) :
    Reach P L (.sp k s .outer, S, n • δ (.side k true false) + n • δ (.side k false true) +
        2 • δ (.d k) + (4 * n) • δ (.c k))
      (after k s, S, n • δ (.side k true false) + n • δ (.side k false false)) := by
  have h1 := astep0 (S := S) (IsRule.outerZ (P := P) k s hk)
    (m := n • δ (.side k true false) + n • δ (.side k false true) + 2 • δ (.d k) +
      (4 * n) • δ (.c k))
    (m' := n • δ (.side k true false) + n • δ (.side k false true) + δ (.d k) +
      (4 * n) • δ (.c k))
    (by intro p; rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;>
      simp <;> split_ifs <;> omega)
    (by mk_eq)
  have h2 := reach_frame (test_run (P := P) (L := L) (S := S) (.si k s false) k false false rfl
      rfl rfl n) (m0 := n • δ (.side k true false) + δ (.d k) + (2 * n) • δ (.c k))
    (m := n • δ (.side k true false) + n • δ (.side k false true) + δ (.d k) +
      (4 * n) • δ (.c k))
    (m' := n • δ (.side k true false) + n • δ (.side k false true) + δ (.d k) +
      (2 * n) • δ (.c k))
    (by mk_eq) (by mk_eq)
  have h3 := astep0 (S := S) (IsRule.siF (P := P) k s hk)
    (m := n • δ (.side k true false) + n • δ (.side k false true) + δ (.d k) +
      (2 * n) • δ (.c k))
    (m' := n • δ (.side k true false) + n • δ (.side k false true) + δ (.d k) +
      (2 * n) • δ (.c k))
    (fun p => by simp) (mv_nn _)
  have h4 := reach_frame (resti_loop (P := P) (S := S) (s := s) hk n n le_rfl)
    (m0 := n • δ (.side k true false) + δ (.d k) + (2 * n) • δ (.c k))
    (m := n • δ (.side k true false) + n • δ (.side k false true) + δ (.d k) +
      (2 * n) • δ (.c k))
    (m' := n • δ (.side k true false) + n • δ (.side k false false) + δ (.d k) +
      (2 * n) • δ (.c k))
    (by mk_eq) (by mk_eq)
  have h5 := astep0 (S := S) (IsRule.restiZ (P := P) k s hk)
    (m := n • δ (.side k true false) + n • δ (.side k false false) + δ (.d k) +
      (2 * n) • δ (.c k))
    (m' := n • δ (.side k true false) + n • δ (.side k false false) + (2 * n) • δ (.c k))
    (by intro p; rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;>
      simp <;> split_ifs <;> omega)
    (by mk_eq)
  have h6 := reach_frame (test_run (P := P) (L := L) (S := S) (.si k s true) k false true rfl
      rfl rfl n) (m0 := n • δ (.side k true false))
    (m := n • δ (.side k true false) + n • δ (.side k false false) + (2 * n) • δ (.c k))
    (m' := n • δ (.side k true false) + n • δ (.side k false false))
    (by mk_eq) (by mk_eq)
  have h7 := astep0 (S := S) (IsRule.siT (P := P) k s hk)
    (m := n • δ (.side k true false) + n • δ (.side k false false))
    (m' := n • δ (.side k true false) + n • δ (.side k false false))
    (fun p => by simp) (mv_nn _)
  exact (((((h2.head h1).tail h3).trans h4).tail h5).trans h6).tail h7

theorem loop_run' (hk : k < L) (n : ℕ) :
    Reach P L (.sp k s .inner, S, (n + 1) • δ (.side k true false) +
        (n + 1) • δ (.side k false false) + (2 * (n + 1) + 2) • δ (.d k) +
        (2 * (n + 1) * (2 * (n + 1) + 2)) • δ (.c k))
      (after k s, S, (n + 1) • δ (.side k true false) + (n + 1) • δ (.side k false false) +
        ((n + 1) * (n + 1)) • δ (tgt k s)) := by
  have h1 := reach_frame (iter_run (P := P) (S := S) (s := s) hk (n + 1))
    (m0 := n • δ (.side k false false) + (2 * n) • δ (.d k) + (4 * (n + 1) * n) • δ (.c k) +
      2 • δ (.d k) + (4 * (n + 1)) • δ (.c k))
    (m := (n + 1) • δ (.side k true false) + (n + 1) • δ (.side k false false) +
      (2 * (n + 1) + 2) • δ (.d k) + (2 * (n + 1) * (2 * (n + 1) + 2)) • δ (.c k))
    (m' := (n + 1) • δ (.side k true false) + n • δ (.side k false false) +
      1 • δ (.side k false true) + (2 * n) • δ (.d k) + (4 * (n + 1) * n) • δ (.c k) +
      (1 * (n + 1)) • δ (tgt k s) + (2 • δ (.d k) + (4 * (n + 1)) • δ (.c k)))
    (by mk_eq')
    (by rcases s with r0 | b0 <;> (try cases r0) <;> (try cases b0) <;> (try simp only [tgt]) <;>
      mk_eq')
  have h2 := reach_add (outer_iter (P := P) (S := S) (s := s) hk (n + 1) n 1)
    (2 • δ (.d k) + (4 * (n + 1)) • δ (.c k))
  have h3 := reach_frame (final_run (P := P) (S := S) (s := s) hk (n + 1))
    (m0 := ((n + 1) * (n + 1)) • δ (tgt k s))
    (m := (n + 1) • δ (.side k true false) + (1 + n) • δ (.side k false true) +
      ((1 + n) * (n + 1)) • δ (tgt k s) + (2 • δ (.d k) + (4 * (n + 1)) • δ (.c k)))
    (m' := (n + 1) • δ (.side k true false) + (n + 1) • δ (.side k false false) +
      ((n + 1) * (n + 1)) • δ (tgt k s))
    (by rcases s with r0 | b0 <;> (try cases r0) <;> (try cases b0) <;> (try simp only [tgt]) <;>
      mk_eq')
    (by rcases s with r0 | b0 <;> (try cases r0) <;> (try cases b0) <;> (try simp only [tgt]) <;>
      mk_eq')
  exact (h1.trans h2).trans h3

/-- **The run of a multiplication loop.** -/
theorem loop_run (hk : k < L) :
    Reach P L (.sp k s .inner, S, B k • δ (.side k true false) +
        B k • δ (.side k false false) + (2 * B k + 2) • δ (.d k) +
        (2 * B k * (2 * B k + 2)) • δ (.c k))
      (after k s, S, B k • δ (.side k true false) + B k • δ (.side k false false) +
        B (k + 1) • δ (tgt k s)) := by
  obtain ⟨n, hn⟩ : ∃ n, B k = n + 1 := ⟨B k - 1, by have := B_pos k; omega⟩
  rw [B_succ, hn]
  exact loop_run' hk n

end loop

end Amp

end HTN
