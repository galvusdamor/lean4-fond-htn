import ComplexityTheory.TOtoHD.Amp.Sound
/-!
# The amplifier: building runs

Tools for the completeness direction: single steps with explicit markings, the frame rule
(`reach_add`: tokens that are not touched can be added to both ends of a run), and the run of an
honest zero test (`test_run`).
-/

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

/-- One token on a place. -/
def δ (p : Pl) : Mk := Pi.single p 1

@[simp] theorem δ_apply (p q : Pl) : δ p q = if q = p then 1 else 0 := by
  simp [δ, Pi.single_apply]

/-- Pointwise proof of an equality of explicit markings. -/
macro "mk_eq" : tactic => `(tactic| (
  funext p
  simp only [mv, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, δ_apply, smul_eq_mul,
    List.count_cons, List.count_nil, beq_iff_eq]
  rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;> simp <;>
    (try split_ifs) <;> omega))

/-- Reachability in the vector addition system. -/
abbrev Reach (P : CM Q Φ) (L : ℕ) : ACfg Q Φ → ACfg Q Φ → Prop :=
  Relation.ReflTransGen (AStep P L)

theorem astep_of {P : CM Q Φ} {L : ℕ} {ρ : Rule Q Φ} (hρ : IsRule P L ρ) {S S' : Finset Φ}
    {m m' : Mk} (hpre : ∀ f ∈ ρ.pre, f ∈ S) (hdl : ∀ p, ρ.dl.count p ≤ m p)
    (hm : mv m ρ.dl ρ.il = m') (hS : upd S ρ.add ρ.del = S') :
    AStep P L (ρ.src, S, m) (ρ.dst, S', m') :=
  ⟨ρ, hρ, rfl, hpre, hdl, by rw [hm, hS]⟩

/-- A step of a rule without facts. -/
theorem astep0 {P : CM Q Φ} {L : ℕ} {l l' : Loc Q} {dl il : List Pl}
    (hρ : IsRule P L ⟨l, [], [], [], dl, il, l'⟩) {S : Finset Φ} {m m' : Mk}
    (hdl : ∀ p, dl.count p ≤ m p) (hm : mv m dl il = m') :
    AStep P L (l, S, m) (l', S, m') :=
  astep_of hρ (by simp) hdl hm (upd_nil S)

theorem astep_add {P : CM Q Φ} {L : ℕ} {x y : ACfg Q Φ} (h : AStep P L x y) (m0 : Mk) :
    AStep P L (x.1, x.2.1, x.2.2 + m0) (y.1, y.2.1, y.2.2 + m0) := by
  obtain ⟨ρ, hρ, hsrc, hpre, hdl, rfl⟩ := h
  refine ⟨ρ, hρ, hsrc, hpre, fun p => le_trans (hdl p) (by simp), ?_⟩
  simp only [Prod.mk.injEq, true_and]
  funext p
  have := hdl p
  simp only [mv, Pi.add_apply]
  omega

/-- **The frame rule.** -/
theorem reach_add {P : CM Q Φ} {L : ℕ} {l l' : Loc Q} {S S' : Finset Φ} {m m' : Mk}
    (h : Reach P L (l, S, m) (l', S', m')) (m0 : Mk) :
    Reach P L (l, S, m + m0) (l', S', m' + m0) := by
  have key : ∀ x y, Reach P L x y → Reach P L (x.1, x.2.1, x.2.2 + m0) (y.1, y.2.1, y.2.2 + m0) := by
    intro x y hxy
    induction hxy with
    | refl => exact .refl
    | tail _ hbc ih => exact .tail ih (astep_add hbc m0)
  exact key _ _ h

theorem reach_of_eq {P : CM Q Φ} {L : ℕ} {x y : ACfg Q Φ} (h : x = y) : Reach P L x y :=
  h ▸ .refl

/-- Lifting a run through the frame rule with marking equalities. -/
theorem reach_frame {P : CM Q Φ} {L : ℕ} {l l' : Loc Q} {S S' : Finset Φ} {m m' a a' m0 : Mk}
    (h : Reach P L (l, S, a) (l', S', a')) (hm : m = a + m0) (hm' : m' = a' + m0) :
    Reach P L (l, S, m) (l', S', m') := by
  rw [hm, hm']; exact reach_add h m0

/-! ### Honest zero tests -/

section test

variable {P : CM Q Φ} {L : ℕ} {S : Finset Φ}

theorem mv_zAA (l : ℕ) (r b : Bool) (n j : ℕ) (hj : j + 1 ≤ n) :
    mv ((n - j) • δ (.side l r (!b)) + j • δ (.side l r b) + (2 * n - j) • δ (.c l)) [.c l] [] =
      (n - j) • δ (.side l r (!b)) + j • δ (.side l r b) + (2 * n - j - 1) • δ (.c l) := by
  cases r <;> cases b <;> mk_eq

theorem dl_zAA (l : ℕ) (r b : Bool) (n j : ℕ) (hj : j + 1 ≤ n) (p : Pl) :
    List.count p [.c l] ≤
      ((n - j) • δ (.side l r (!b)) + j • δ (.side l r b) + (2 * n - j) • δ (.c l)) p := by
  cases r <;> cases b <;> (rcases p with ⟨k', r', b'⟩ | k' | k' <;>
    (try cases r') <;> (try cases b') <;> simp <;> split_ifs <;> omega)

theorem mv_zA'A (l : ℕ) (r b : Bool) (n j : ℕ) (hj : j + 1 ≤ n) :
    mv ((n - j) • δ (.side l r (!b)) + j • δ (.side l r b) + (2 * n - j - 1) • δ (.c l))
        [.side l r (!b)] [.side l r b] =
      (n - (j + 1)) • δ (.side l r (!b)) + (j + 1) • δ (.side l r b) +
        (2 * n - (j + 1)) • δ (.c l) := by
  cases r <;> cases b <;> mk_eq

theorem dl_zA'A (l : ℕ) (r b : Bool) (n j : ℕ) (hj : j + 1 ≤ n) (p : Pl) :
    List.count p [.side l r (!b)] ≤
      ((n - j) • δ (.side l r (!b)) + j • δ (.side l r b) + (2 * n - j - 1) • δ (.c l)) p := by
  cases r <;> cases b <;> (rcases p with ⟨k', r', b'⟩ | k' | k' <;>
    (try cases r') <;> (try cases b') <;> simp <;> split_ifs <;> omega)

theorem test_A (z : ZI) (l : ℕ) (r b : Bool) (hl : z.lvl L = l) (hr : z.pr = r) (hb : z.sd = b)
    (n : ℕ) : ∀ j ≤ n, Reach P L (.zt z .A, S, n • δ (.side l r (!b)) + (2 * n) • δ (.c l))
      (.zt z .A, S, (n - j) • δ (.side l r (!b)) + j • δ (.side l r b) +
        (2 * n - j) • δ (.c l)) := by
  intro j
  induction j with
  | zero => intro _; apply reach_of_eq; congr 2; simp
  | succ j ih =>
    intro hj
    have h1 := astep0 (S := S) (IsRule.zAA (P := P) (L := L) z)
      (m := (n - j) • δ (.side l r (!b)) + j • δ (.side l r b) + (2 * n - j) • δ (.c l))
      (m' := (n - j) • δ (.side l r (!b)) + j • δ (.side l r b) + (2 * n - j - 1) • δ (.c l))
      (by rw [hl]; exact dl_zAA l r b n j hj) (by rw [hl]; exact mv_zAA l r b n j hj)
    have h2 := astep0 (S := S) (IsRule.zA'A (P := P) (L := L) z)
      (m := (n - j) • δ (.side l r (!b)) + j • δ (.side l r b) + (2 * n - j - 1) • δ (.c l))
      (m' := (n - (j + 1)) • δ (.side l r (!b)) + (j + 1) • δ (.side l r b) +
        (2 * n - (j + 1)) • δ (.c l))
      (by rw [hl, hr, hb]; exact dl_zA'A l r b n j hj)
      (by rw [hl, hr, hb]; exact mv_zA'A l r b n j hj)
    exact ((ih (by omega)).tail h1).tail h2

theorem mv_zBB (l : ℕ) (r b : Bool) (n j : ℕ) (hj : j + 1 ≤ n) :
    mv ((n - j) • δ (.side l r b) + j • δ (.side l r (!b)) + (n - j) • δ (.c l)) [.c l] [] =
      (n - j) • δ (.side l r b) + j • δ (.side l r (!b)) + (n - j - 1) • δ (.c l) := by
  cases r <;> cases b <;> mk_eq

theorem dl_zBB (l : ℕ) (r b : Bool) (n j : ℕ) (hj : j + 1 ≤ n) (p : Pl) :
    List.count p [.c l] ≤
      ((n - j) • δ (.side l r b) + j • δ (.side l r (!b)) + (n - j) • δ (.c l)) p := by
  cases r <;> cases b <;> (rcases p with ⟨k', r', b'⟩ | k' | k' <;>
    (try cases r') <;> (try cases b') <;> simp <;> split_ifs <;> omega)

theorem mv_zB'B (l : ℕ) (r b : Bool) (n j : ℕ) (hj : j + 1 ≤ n) :
    mv ((n - j) • δ (.side l r b) + j • δ (.side l r (!b)) + (n - j - 1) • δ (.c l))
        [.side l r b] [.side l r (!b)] =
      (n - (j + 1)) • δ (.side l r b) + (j + 1) • δ (.side l r (!b)) +
        (n - (j + 1)) • δ (.c l) := by
  cases r <;> cases b <;> mk_eq

theorem dl_zB'B (l : ℕ) (r b : Bool) (n j : ℕ) (hj : j + 1 ≤ n) (p : Pl) :
    List.count p [.side l r b] ≤
      ((n - j) • δ (.side l r b) + j • δ (.side l r (!b)) + (n - j - 1) • δ (.c l)) p := by
  cases r <;> cases b <;> (rcases p with ⟨k', r', b'⟩ | k' | k' <;>
    (try cases r') <;> (try cases b') <;> simp <;> split_ifs <;> omega)

theorem test_B (z : ZI) (l : ℕ) (r b : Bool) (hl : z.lvl L = l) (hr : z.pr = r) (hb : z.sd = b)
    (n : ℕ) : ∀ j ≤ n, Reach P L (.zt z .B, S, n • δ (.side l r b) + 0 • δ (.side l r (!b)) +
        n • δ (.c l))
      (.zt z .B, S, (n - j) • δ (.side l r b) + j • δ (.side l r (!b)) +
        (n - j) • δ (.c l)) := by
  intro j
  induction j with
  | zero => intro _; apply reach_of_eq; simp
  | succ j ih =>
    intro hj
    have h1 := astep0 (S := S) (IsRule.zBB (P := P) (L := L) z)
      (m := (n - j) • δ (.side l r b) + j • δ (.side l r (!b)) + (n - j) • δ (.c l))
      (m' := (n - j) • δ (.side l r b) + j • δ (.side l r (!b)) + (n - j - 1) • δ (.c l))
      (by rw [hl]; exact dl_zBB l r b n j hj) (by rw [hl]; exact mv_zBB l r b n j hj)
    have h2 := astep0 (S := S) (IsRule.zB'B (P := P) (L := L) z)
      (m := (n - j) • δ (.side l r b) + j • δ (.side l r (!b)) + (n - j - 1) • δ (.c l))
      (m' := (n - (j + 1)) • δ (.side l r b) + (j + 1) • δ (.side l r (!b)) +
        (n - (j + 1)) • δ (.c l))
      (by rw [hl, hr, hb]; exact dl_zB'B l r b n j hj)
      (by rw [hl, hr, hb]; exact mv_zB'B l r b n j hj)
    exact ((ih (by omega)).tail h1).tail h2

/-- **An honest zero test**: the tested side is empty, the other side holds `n` tokens; the test
moves them over and back, consuming `2 n` move tokens. -/
theorem test_run (z : ZI) (l : ℕ) (r b : Bool) (hl : z.lvl L = l) (hr : z.pr = r)
    (hb : z.sd = b) (n : ℕ) :
    Reach P L (.zt z .A, S, n • δ (.side l r (!b)) + (2 * n) • δ (.c l))
      (.zt z .B, S, n • δ (.side l r (!b))) := by
  have hA := test_A (P := P) (S := S) z l r b hl hr hb n n le_rfl
  have hAB := astep0 (S := S) (IsRule.zAB (P := P) (L := L) z)
    (m := (n - n) • δ (.side l r (!b)) + n • δ (.side l r b) + (2 * n - n) • δ (.c l))
    (m' := n • δ (.side l r b) + 0 • δ (.side l r (!b)) + n • δ (.c l))
    (fun p => by simp) (by cases r <;> cases b <;> mk_eq)
  have hB := test_B (P := P) (S := S) z l r b hl hr hb n n le_rfl
  refine ((hA.tail hAB).trans hB).trans (reach_of_eq ?_)
  congr 2
  cases r <;> cases b <;> mk_eq

end test

end Amp

end HTN
