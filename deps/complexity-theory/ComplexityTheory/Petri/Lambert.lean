import ComplexityTheory.Petri.GP
/-!
# Lambert's iteration lemma: perfect generalised problems are solvable

**Block lemma** (`block_lemma`).  Let `b` be a well-formed block with a strongly connected
component, `t` a solution and `h` a homogeneous solution of its characteristic constraints, `u` a
forward and `v` a backward pumping cycle, and assume that `h` is large compared with `u` and `v`
(`h.ψ ≥ Pu + Pv + 1` on all edges, `h.M₁ j ≥ 2|u|a + 1` on the ω-coordinates of the input,
`h.M' j ≥ 2|v|a + 1` on those of the output; `a` bounds the edge vectors).  Then for all large
`n` there is a run of the component from `t.M₁ + n h.M₁` to `t.M' + n h.M'`, namely
`u^n w^(n-1) z v^n`, where `w` is an Euler cycle at the entry with Parikh vector
`h.ψ - Pu - Pv` and `z` an Euler path from the entry to the exit with Parikh vector
`t.ψ + h.ψ - Pu - Pv`.

On a coordinate that is finite in the labels the run follows the labels.  On an ω-coordinate,
with `P₁ : 1 ≤ h.M₁ + Eu`, `P₂ : 1 ≤ h.M' - Ev` (both hold in each of the four cases
finite/ω input/output), the value before the `i`-th copy of `w` is
`t.M₁ + (n-i)(h.M₁ + Eu) + i (h.M' - Ev) ≥ n`.

**Lambert's theorem** (`solvable_of_perfect`): a perfect generalised problem is solvable — scale
the homogeneous solution by a common factor and apply the block lemma to every block.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp

variable {ι : Type*} {C : Comp ι}

/-! ### Helpers -/

theorem walk_rep {u : ℕ} {π : List ℕ} (h : Walk C u π u) (n : ℕ) :
    Walk C u (List.replicate n π).flatten u := by
  induction n with
  | zero => exact Euler.Walk.nil _
  | succ n ih => rw [List.replicate_succ, List.flatten_cons]; exact Euler.Walk.append h ih

theorem posReach_of_walk {E : List (ℕ × ℕ)} {ψ : ℕ → ℕ} (hpos : ∀ k < E.length, 0 < ψ k)
    {s t : ℕ} {π : List ℕ} (hw : Euler.Walk E s π t) : PosReach E ψ s t := by
  induction hw with
  | nil => exact Relation.ReflTransGen.refl
  | @cons k π v hk _ ih =>
    exact Relation.ReflTransGen.head ⟨k, hk, hpos k hk, rfl, rfl⟩ ih

theorem psum_add (C : Comp ι) (φ ψ : ℕ → ℕ) : psum C (φ + ψ) = psum C φ + psum C ψ := by
  unfold psum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [add_smul]

theorem psum_smul (C : Comp ι) (n : ℕ) (φ : ℕ → ℕ) : psum C (n • φ) = (n : ℤ) • psum C φ := by
  unfold psum
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_smul]

theorem psum_congr (C : Comp ι) {φ ψ : ℕ → ℕ} (h : ∀ k < C.edges.length, φ k = ψ k) :
    psum C φ = psum C ψ :=
  Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.1 hk)]

theorem eff_eq_psum {s t : ℕ} {π : List ℕ} (hw : Walk C s π t) :
    C.eff π = psum C (fun k => π.count k) :=
  eff_eq_sum π hw.lt'

theorem count_eq_zero_of_walk {s t : ℕ} {π : List ℕ} (hw : Walk C s π t) {k : ℕ}
    (hk : C.edges.length ≤ k) : π.count k = 0 := by
  rw [List.count_eq_zero]
  intro h
  have := hw.lt' k h
  omega

/-- Euler's theorem in the form used here: a flow positive on every edge of a strongly
connected component, satisfying Kirchhoff's law from `s` to `t`, is the Parikh vector of a walk. -/
theorem exists_walk_of_flow (hWF : WF C) (hS : SC C) {ψ : ℕ → ℕ} {s t : ℕ} (hs : s ∈ C.nodes)
    (hK : Kirch C.gr ψ s t) (hpos : ∀ k < C.edges.length, 0 < ψ k) :
    ∃ π, Walk C s π t ∧ ∀ k < C.edges.length, π.count k = ψ k := by
  have hC : Conn C.gr ψ s := by
    intro k hk _
    rw [gr_length] at hk
    obtain ⟨π, hπ⟩ := hS s hs _ (hWF.1 k hk).1
    exact posReach_of_walk (fun k hk => hpos k (by rwa [gr_length] at hk)) hπ
  obtain ⟨π, hπ, hc⟩ := euler (E := C.gr) _ ψ s t rfl hK hC
  exact ⟨π, hπ, fun k hk => hc k (by rwa [gr_length])⟩

/-! ### Arithmetic facts for the block lemma -/

theorem arith_u (M₁ H eu U : ℤ) (n i : ℕ) (hM : 0 ≤ M₁) (hH : 2 * U + 1 ≤ H) (he : -U ≤ eu)
    (hU : 0 ≤ U) (hi : i ≤ n) (hn : 1 ≤ n) : U ≤ M₁ + n * H + i * eu := by
  have hi' : (i : ℤ) ≤ n := by exact_mod_cast hi
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have h1 : (i : ℤ) * eu ≥ -(n * U) := by
    have : (i : ℤ) * (eu + U) ≥ 0 := mul_nonneg (by positivity) (by linarith)
    nlinarith
  have h2 : (n : ℤ) * H ≥ n * (2 * U + 1) := mul_le_mul_of_nonneg_left hH (by positivity)
  nlinarith

theorem arith_mid (M₁ H₁ H' eu ev ew : ℤ) (m i : ℕ) (hM : 0 ≤ M₁) (h1 : 1 ≤ H₁ + eu)
    (h2 : 1 ≤ H' - ev) (hΔ : H' = H₁ + ew + eu + ev) (hi : i ≤ m + 1) :
    (m : ℤ) ≤ M₁ + (m + 2) * H₁ + (m + 2) * eu + i * ew := by
  have hi' : (i : ℤ) ≤ m + 1 := by exact_mod_cast hi
  have e1 : M₁ + (m + 2) * H₁ + (m + 2) * eu + i * ew =
      M₁ + ((m + 2 : ℤ) - i) * (H₁ + eu) + i * (H' - ev) := by rw [hΔ]; ring
  rw [e1]
  have : (0 : ℤ) ≤ ((m + 2 : ℤ) - i) * (H₁ + eu - 1) := mul_nonneg (by linarith) (by linarith)
  have : (0 : ℤ) ≤ (i : ℤ) * (H' - ev - 1) := mul_nonneg (by positivity) (by linarith)
  nlinarith

theorem arith_v (M' H' ev V : ℤ) (m i : ℕ) (hM : 0 ≤ M') (hH : 2 * V + 1 ≤ H') (he : ev ≤ V)
    (hV : 0 ≤ V) (hi : i ≤ m + 1) : V ≤ M' + (m + 2) * H' - (m + 2) * ev + i * ev := by
  have hi' : (i : ℤ) ≤ m + 1 := by exact_mod_cast hi
  have h1 : ((m + 2 : ℤ) - i) * ev ≤ ((m + 2 : ℤ) - i) * V :=
    mul_le_mul_of_nonneg_left he (by linarith)
  have h2 : ((m + 2 : ℤ) - i) * V ≤ (m + 2) * V :=
    mul_le_mul_of_nonneg_right (by linarith [(Nat.cast_nonneg i : (0 : ℤ) ≤ i)]) hV
  have h3 : ((m + 2 : ℤ)) * H' ≥ (m + 2) * (2 * V + 1) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  nlinarith

theorem arith_v' (y ev : ℤ) (m i : ℕ) (he : ev ≤ -1) (hi : i ≤ m + 1) :
    y - ev ≤ y - (m + 2) * ev + i * ev := by
  have hi' : (i : ℤ) ≤ m + 1 := by exact_mod_cast hi
  have : ((m + 2 : ℤ) - i - 1) * ev ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith

/-! ### The block lemma -/

variable [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem block_lemma {b : Block ι} (hW : WFB b) (hS : SC b.comp) {t h : Tri ι} (ht : CharOK b t)
    (hh : HomOK b h)
    {u v : List ℕ} (hu : Walk b.comp b.comp.entry u b.comp.entry)
    (huF : FiresOn b.comp (fun j => b.inp j ≠ ⊤) (fin0 b.inp) u)
    (huE : ∀ j, b.inp j ≠ ⊤ → b.comp.lab b.comp.entry j = ⊤ → 1 ≤ b.comp.eff u j)
    (hv : Walk b.comp b.comp.exit v b.comp.exit)
    (hvF : FiresOn b.comp (fun j => b.out j ≠ ⊤) (fin0 b.out - b.comp.eff v) v)
    (hvE : ∀ j, b.out j ≠ ⊤ → b.comp.lab b.comp.exit j = ⊤ → b.comp.eff v j ≤ -1)
    (hΔ : ∀ k < b.comp.edges.length, u.count k + v.count k + 1 ≤ h.ψ k)
    (hH₁ : ∀ j, b.inp j = ⊤ → 2 * u.length * b.comp.amax + 1 ≤ h.M₁ j)
    (hH' : ∀ j, b.out j = ⊤ → 2 * v.length * b.comp.amax + 1 ≤ h.M' j) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ π, Walk b.comp b.comp.entry π b.comp.exit ∧
      FiresOn b.comp (fun _ => True) (t.M₁ + (n : ℤ) • h.M₁) π ∧
      LabOn b.comp (fun _ => True) b.comp.entry (t.M₁ + (n : ℤ) • h.M₁) π ∧
      t.M₁ + (n : ℤ) • h.M₁ + b.comp.eff π = t.M' + (n : ℤ) • h.M' := by
  obtain ⟨hWF, hM, hin, hout⟩ := hW
  obtain ⟨htM₁, htA, htK, htE, htM', htA'⟩ := ht
  obtain ⟨hhM₁, hhA, hhK, hhE, hhM', hhA'⟩ := hh
  set C := b.comp with hCdef
  set len := C.edges.length
  -- the Euler cycle `w`
  set ψw : ℕ → ℕ := fun k => h.ψ k - u.count k - v.count k with hψw
  have hsplit : h.ψ = ψw + ((fun k => u.count k) + fun k => v.count k) := by
    funext k
    simp only [Pi.add_apply, hψw]
    by_cases hk : k < len
    · have := hΔ k hk; omega
    · rw [count_eq_zero_of_walk hu (by omega), count_eq_zero_of_walk hv (by omega)]; omega
  have hKu : Kirch C.gr (fun k => u.count k) C.entry C.entry := kirch_walk hu
  have hKv : Kirch C.gr (fun k => v.count k) C.entry C.entry :=
    kirch_balanced_iff.1 (kirch_walk hv)
  have hKw : Kirch C.gr ψw C.entry C.entry :=
    kirch_of_add (hsplit ▸ hhK) (kirch_add hKu hKv)
  have hwpos : ∀ k < len, 0 < ψw k := by
    intro k hk; have := hΔ k hk; simp only [hψw]; omega
  obtain ⟨w, hw, hwc⟩ := exists_walk_of_flow hWF hS hWF.2.1 hKw hwpos
  -- the Euler path `z`
  have hKz : Kirch C.gr (t.ψ + ψw) C.entry C.exit := kirch_add htK hKw
  obtain ⟨z, hz, hzc⟩ := exists_walk_of_flow hWF hS hWF.2.1 hKz
    (fun k hk => by have := hwpos k hk; simp only [Pi.add_apply]; omega)
  -- effects
  set a := C.amax
  have ha : 0 ≤ a := amax_nonneg
  have hEu : C.eff u = psum C (fun k => u.count k) := eff_eq_psum hu
  have hEv : C.eff v = psum C (fun k => v.count k) := eff_eq_psum hv
  have hEw : C.eff w = psum C ψw := by rw [eff_eq_psum hw]; exact psum_congr C hwc
  have hEz : C.eff z = psum C (t.ψ + ψw) := by rw [eff_eq_psum hz]; exact psum_congr C hzc
  have hEh : psum C h.ψ = C.eff w + C.eff u + C.eff v := by
    rw [hsplit, psum_add, psum_add, hEu, hEv, hEw]; abel
  refine ⟨2 + u.length * a.toNat + v.length * a.toNat + w.length * a.toNat +
    z.length * a.toNat, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set π := (List.replicate (m + 2) u).flatten ++ (List.replicate (m + 1) w).flatten ++ z ++
    (List.replicate (m + 2) v).flatten with hπ
  have hwalk : Walk C C.entry π C.exit :=
    ((walk_rep hu _).append (walk_rep hw _)).append hz |>.append (walk_rep hv _)
  have heffπ : C.eff π = (t.M' - t.M₁) + ((m + 2 : ℕ) : ℤ) • (h.M' - h.M₁) := by
    simp only [hπ, eff_append, eff_rep]
    rw [hEz, psum_add, ← hEw, sub_eq_of_eq_add' htE, sub_eq_of_eq_add' hhE, hEh]
    simp only [smul_add, natCast_zsmul]
    rw [show (m + 2) • C.eff w = (m + 1) • C.eff w + C.eff w from succ_nsmul _ _]
    abel
  have hcoord : ∀ j, FiresOn C (· = j) (t.M₁ + ((m + 2 : ℕ) : ℤ) • h.M₁) π ∧
      LabOn C (· = j) C.entry (t.M₁ + ((m + 2 : ℕ) : ℤ) • h.M₁) π := by
    intro j
    by_cases hlab : C.lab C.entry j ≠ ⊤
    · -- a coordinate finite in the labels follows the labels
      have hfin : ∀ k < len, C.lab (src C.gr k) j ≠ ⊤ ∧ C.lab (tgt C.gr k) j ≠ ⊤ := fun k hk =>
        ⟨(lab_ne_top_iff' hM hS hWF.2.1 (hWF.1 k hk).1).1 hlab,
          (lab_ne_top_iff' hM hS hWF.2.1 (hWF.1 k hk).2).1 hlab⟩
      suffices hx : (t.M₁ + ((m + 2 : ℕ) : ℤ) • h.M₁) j = (C.lab C.entry j).toNat by
        have := labOn_of_exact hM.exact hfin hwalk hx
        exact ⟨this.2, this.1⟩
      have h1 := hin j hlab
      have h2 : b.inp j ≠ ⊤ := h1 ▸ hlab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhA j h2, mul_zero, add_zero]
      rw [htA j h2, h1]
    · push_neg at hlab
      have hlab' : C.lab C.exit j = ⊤ := by
        by_contra hne
        exact (lab_ne_top_iff' hM hS hWF.2.1 hWF.2.2).2 hne hlab
      have htop : ∀ k < len, C.lab (tgt C.gr k) j = ⊤ := fun k hk => by
        by_contra hne
        exact (lab_ne_top_iff' hM hS hWF.2.1 (hWF.1 k hk).2).2 hne hlab
      refine ⟨?_, labOn_of_top htop hwalk hlab _⟩
      have hUa : |C.eff u j| ≤ u.length * a := abs_eff_le u hu.lt' j
      have hVa : |C.eff v j| ≤ v.length * a := abs_eff_le v hv.lt' j
      have hu0 : (0 : ℤ) ≤ u.length * a := by positivity
      have hv0 : (0 : ℤ) ≤ v.length * a := by positivity
      have hΔj : h.M' j = h.M₁ j + C.eff w j + C.eff u j + C.eff v j := by
        rw [hhE, Pi.add_apply, hEh]; simp only [Pi.add_apply]; ring
      have P1 : 1 ≤ h.M₁ j + C.eff u j := by
        by_cases hi : b.inp j = ⊤
        · have := hH₁ j hi
          have := neg_abs_le (C.eff u j)
          linarith
        · rw [hhA j hi]; simpa using huE j hi hlab
      have P2 : 1 ≤ h.M' j - C.eff v j := by
        by_cases ho : b.out j = ⊤
        · have := hH' j ho
          have := le_abs_self (C.eff v j)
          linarith
        · rw [hhA' j ho]; have := hvE j ho hlab'; linarith
      have haN : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
      have hwl : (w.length : ℤ) * a ≤ m := by
        have : w.length * a.toNat ≤ m := by omega
        have := (Nat.cast_le (α := ℤ)).2 this
        push_cast at this; rwa [haN] at this
      have hzl : (z.length : ℤ) * a ≤ m := by
        have : z.length * a.toNat ≤ m := by omega
        have := (Nat.cast_le (α := ℤ)).2 this
        push_cast at this; rwa [haN] at this
      have hXj : (t.M₁ + ((m + 2 : ℕ) : ℤ) • h.M₁) j = t.M₁ j + (m + 2) * h.M₁ j := by
        simp [Pi.add_apply, smul_eq_mul]
      rw [hπ, firesOn_append, firesOn_append, firesOn_append]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · -- `u^(m+2)`
        rw [firesOn_rep _ _ _ (by omega)]
        intro i hi
        by_cases hinp : b.inp j = ⊤
        · refine firesOn_of_ge hu.lt' ?_
          simp only [Pi.add_apply, hXj, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
          have := arith_u (t.M₁ j) (h.M₁ j) (C.eff u j) (u.length * a) (m + 2) i (htM₁ j)
            (by linarith [hH₁ j hinp]) (by linarith [neg_abs_le (C.eff u j)]) hu0 hi.le (by omega)
          push_cast at this
          linarith
        · refine firesOn_mono (huF.single hinp) ?_
          simp only [Pi.add_apply, hXj, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, hhA j hinp, mul_zero,
            add_zero]
          rw [htA j hinp]
          have := huE j hinp hlab
          simp only [fin0]
          have : (0 : ℤ) ≤ i * C.eff u j := mul_nonneg (by positivity) (by linarith)
          linarith
      · -- `w^(m+1)`
        rw [firesOn_rep _ _ _ (by omega)]
        intro i hi
        refine firesOn_of_ge hw.lt' ?_
        simp only [Pi.add_apply, hXj, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, eff_rep]
        have := arith_mid (t.M₁ j) (h.M₁ j) (h.M' j) (C.eff u j) (C.eff v j) (C.eff w j) m i
          (htM₁ j) P1 P2 hΔj hi.le
        push_cast at this ⊢
        linarith
      · -- `z`
        refine firesOn_of_ge hz.lt' ?_
        simp only [Pi.add_apply, hXj, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, eff_append, eff_rep]
        have := arith_mid (t.M₁ j) (h.M₁ j) (h.M' j) (C.eff u j) (C.eff v j) (C.eff w j) m
          (m + 1) (htM₁ j) P1 P2 hΔj le_rfl
        push_cast at this ⊢
        linarith
      · -- `v^(m+2)`
        have hY : (t.M₁ + ((m + 2 : ℕ) : ℤ) • h.M₁ +
            C.eff ((List.replicate (m + 2) u).flatten ++ (List.replicate (m + 1) w).flatten ++
              z)) j = t.M' j + (m + 2) * h.M' j - (m + 2) * C.eff v j := by
          have h1 := congrFun heffπ j
          simp only [hπ, eff_append, eff_rep, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
            nsmul_eq_mul, smul_eq_mul] at h1 ⊢
          push_cast at h1 ⊢
          simp only [Pi.mul_apply, Pi.add_apply, Pi.natCast_apply, Pi.ofNat_apply] at h1 ⊢
          linarith
        rw [firesOn_rep _ _ _ (by omega)]
        intro i hi
        have hi' : i ≤ m + 1 := Nat.lt_succ_iff.1 hi
        by_cases hout' : b.out j = ⊤
        · refine firesOn_of_ge hv.lt' ?_
          simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at hY ⊢
          rw [hY]
          exact arith_v (t.M' j) (h.M' j) (C.eff v j) (v.length * a) m i (htM' j) (by linarith [hH' j hout'])
            (le_trans (le_abs_self _) hVa) hv0 hi'
        · refine firesOn_mono (hvF.single hout') ?_
          simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at hY ⊢
          rw [hY, hhA' j hout', htA' j hout']
          simp only [Pi.sub_apply, fin0, mul_zero, add_zero]
          exact arith_v' _ _ m i (hvE j hout' hlab') hi'
  refine ⟨π, hwalk, firesOn_of_forall fun j _ => (hcoord j).1,
    labOn_of_forall fun j _ => (hcoord j).2, ?_⟩
  rw [heffπ, smul_sub]; abel

/-! ### Lambert's theorem -/

/-- Scaling a candidate solution. -/
def Tri.smul (c : ℕ) (h : Tri ι) : Tri ι := ⟨(c : ℤ) • h.M₁, c • h.ψ, (c : ℤ) • h.M'⟩

theorem homOK_smul {b : Block ι} {h : Tri ι} (hh : HomOK b h) (c : ℕ) : HomOK b (h.smul c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hh
  refine ⟨fun j => ?_, fun j hj => ?_, kirch_smul c h3, ?_, fun j => ?_, fun j hj => ?_⟩
  · simp only [Tri.smul, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (h1 j)
  · simp [Tri.smul, h2 j hj]
  · simp only [Tri.smul, psum_smul, h4, smul_add]
  · simp only [Tri.smul, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (h5 j)
  · simp [Tri.smul, h6 j hj]

/-- The block lemma in the form of a run through the block, for every large scaling factor. -/
theorem block_ok {b : Block ι} (hW : WFB b) (hS : SC b.comp) (hF : PumpF b) (hB : PumpB b)
    {t h : Tri ι} (ht : CharOK b t) (hh : HomOK b h) (hfull : Full b h) :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      BlockRun b (t.M₁ + ((n * c : ℕ) : ℤ) • h.M₁ - b.pre) (t.M' + ((n * c : ℕ) : ℤ) • h.M') := by
  obtain ⟨esu, hesu, hesuF, hesuE⟩ := hF
  obtain ⟨u, hu, rfl⟩ := hesu.toIdx
  have huF := firesOn_iff_tfires.2 hesuF
  have huE : ∀ j, b.inp j ≠ ⊤ → b.comp.lab b.comp.entry j = ⊤ → 1 ≤ b.comp.eff u j := by
    intro j h1 h2; rw [← teff_map_edge]; exact hesuE j h1 h2
  obtain ⟨esv, hesv, hesvF, hesvE⟩ := hB
  obtain ⟨v, hv, rfl⟩ := hesv.toIdx
  have hvF : FiresOn b.comp (fun j => b.out j ≠ ⊤) (fin0 b.out - b.comp.eff v) v := by
    rw [← teff_map_edge]; exact firesOn_iff_tfires.2 hesvF
  have hvE : ∀ j, b.out j ≠ ⊤ → b.comp.lab b.comp.exit j = ⊤ → b.comp.eff v j ≤ -1 := by
    intro j h1 h2; rw [← teff_map_edge]; exact hesvE j h1 h2
  set a := b.comp.amax
  have ha : 0 ≤ a := amax_nonneg
  refine ⟨(∑ k ∈ range b.comp.edges.length, (u.count k + v.count k + 1)) +
    2 * u.length * a.toNat + 2 * v.length * a.toNat + 1, fun c hc => ?_⟩
  have haN : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
  have hc' : ((2 * u.length * a.toNat + 2 * v.length * a.toNat + 1 : ℕ) : ℤ) ≤ c := by
    exact_mod_cast le_trans (by omega) hc
  push_cast at hc'
  rw [haN] at hc'
  have hu0 : (0 : ℤ) ≤ u.length * a := by positivity
  have hv0 : (0 : ℤ) ≤ v.length * a := by positivity
  obtain ⟨n₀, hn₀⟩ := block_lemma hW hS ht (homOK_smul hh c) hu huF huE hv hvF hvE
    (fun k hk => by
      have h1 : u.count k + v.count k + 1 ≤
          ∑ k ∈ range b.comp.edges.length, (u.count k + v.count k + 1) :=
        Finset.single_le_sum (f := fun k => u.count k + v.count k + 1) (fun _ _ => by omega)
          (Finset.mem_range.2 hk)
      have h2 := hfull.1 k hk
      simp only [Tri.smul, Pi.smul_apply, smul_eq_mul]
      nlinarith)
    (fun j hj => by
      have h2 := hfull.2.1 j hj
      simp only [Tri.smul, Pi.smul_apply, smul_eq_mul]
      nlinarith)
    (fun j hj => by
      have h2 := hfull.2.2 j hj
      simp only [Tri.smul, Pi.smul_apply, smul_eq_mul]
      nlinarith)
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨π, hπ, hfire, hlabπ, heq⟩ := hn₀ n hn
  have e1 : t.M₁ + ((n * c : ℕ) : ℤ) • h.M₁ - b.pre + b.pre = t.M₁ + (n : ℤ) • (h.smul c).M₁ := by
    simp only [Tri.smul, sub_add_cancel, smul_smul]; push_cast; ring_nf
  have e2 : t.M' + ((n * c : ℕ) : ℤ) • h.M' = t.M' + (n : ℤ) • (h.smul c).M' := by
    simp only [Tri.smul, smul_smul]; push_cast; ring_nf
  refine ⟨?_, π.map b.comp.edge, hπ.toT, ?_, ?_, ?_, ?_⟩
  · rw [e1]
    intro j hj
    have := ht.2.1 j hj
    simp [Tri.smul, hh.2.1 j hj, this]
  · rw [e1]; exact firesOn_iff_tfires.1 hfire
  · rw [e1]; exact labOn_iff_tlab.1 hlabπ
  · rw [e1, e2, teff_map_edge, heq]
  · rw [e2]
    intro j hj
    have := ht.2.2.2.2.2 j hj
    simp [Tri.smul, hh.2.2.2.2.2 j hj, this]

/-- The start of a list of blocks, for a given scaling. -/
def startOf (k : ℕ) : List (Block ι) → List (Tri ι) → List (Tri ι) → (ι → ℤ)
  | b :: _, t :: _, h :: _ => t.M₁ + (k : ℤ) • h.M₁ - b.pre
  | _, _, _ => 0

omit [Fintype ι] in
theorem LinkedBy.tail {f : (ι → ℤ) → (ι → ℤ) → (ι → ℤ)} {b : Block ι} {bs : List (Block ι)}
    {t : Tri ι} {ts : List (Tri ι)} (h : LinkedBy f (b :: bs) (t :: ts)) : LinkedBy f bs ts := by
  cases bs with
  | nil => cases ts <;> simp [LinkedBy]
  | cons b' bs => cases ts with
    | nil => simp [LinkedBy]
    | cons t' ts => exact h.2

theorem listRun_scaled (bs : List (Block ι)) : ∀ (ts hs : List (Tri ι)),
    (∀ b ∈ bs, WFB b ∧ SC b.comp ∧ PumpF b ∧ PumpB b) → CharSol bs ts → HomSol bs hs →
    List.Forall₂ Full bs hs →
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ M', ListRun bs (startOf (n * c) bs ts hs) M' := by
  induction bs with
  | nil => exact fun _ _ _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨_, rfl⟩⟩⟩
  | cons b bs ih =>
    intro ts hs hb hC hH hF
    obtain ⟨hC1, hC2⟩ := hC
    obtain ⟨hH1, hH2⟩ := hH
    obtain ⟨t, ts, ht, hts, rfl⟩ := List.forall₂_cons_left_iff.1 hC1
    obtain ⟨h, hs, hh, hhs, rfl⟩ := List.forall₂_cons_left_iff.1 hH1
    have hf := (List.forall₂_cons.1 hF).1
    have hfs := (List.forall₂_cons.1 hF).2
    obtain ⟨hW, hS, hPF, hPB⟩ := hb b List.mem_cons_self
    obtain ⟨c₁, hc₁⟩ := block_ok hW hS hPF hPB ht hh hf
    obtain ⟨c₂, hc₂⟩ := ih ts hs (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))
      ⟨hts, hC2.tail⟩ ⟨hhs, hH2.tail⟩ hfs
    refine ⟨max c₁ c₂, fun c hc => ?_⟩
    obtain ⟨n₁, hn₁⟩ := hc₁ c (le_trans (le_max_left _ _) hc)
    obtain ⟨n₂, hn₂⟩ := hc₂ c (le_trans (le_max_right _ _) hc)
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    obtain ⟨M', hM'⟩ := hn₂ n (le_trans (le_max_right _ _) hn)
    have hrun := hn₁ n (le_trans (le_max_left _ _) hn)
    cases bs with
    | nil => exact ⟨_, _, hrun, rfl⟩
    | cons b' bs =>
      obtain ⟨t', ts', -, -, rfl⟩ := List.forall₂_cons_left_iff.1 hts
      obtain ⟨h', hs', -, -, rfl⟩ := List.forall₂_cons_left_iff.1 hhs
      refine ⟨M', _, hrun, ?_⟩
      have e1 : t'.M₁ = t.M' + b'.pre := hC2.1
      have e2 : h'.M₁ = h.M' := hH2.1
      have : startOf (n * c) (b' :: bs) (t' :: ts') (h' :: hs') =
          t.M' + ((n * c : ℕ) : ℤ) • h.M' := by
        simp only [startOf, e1, e2]; abel
      rw [← this]
      exact hM'

/-- **Lambert's theorem**: perfect generalised problems are solvable. -/
theorem solvable_of_perfect {bs : List (Block ι)} (h : Perfect bs) : Solvable bs := by
  obtain ⟨hb, ts, hs, hC, hH, hF⟩ := h
  obtain ⟨c₀, hc₀⟩ := listRun_scaled bs ts hs hb hC hH hF
  obtain ⟨n₀, hn₀⟩ := hc₀ c₀ le_rfl
  obtain ⟨M', hM'⟩ := hn₀ n₀ le_rfl
  exact ⟨_, _, hM'⟩

end KLM

end Petri

end HTN
