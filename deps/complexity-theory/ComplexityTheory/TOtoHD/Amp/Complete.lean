import ComplexityTheory.TOtoHD.Amp.Levels
/-!
# The amplifier: completeness and the main theorem

`complete`: an accepting run of the counter machine with counters at most `B L` is simulated by
an accepting run of the vector addition system (set up the levels with exactly the budgets the
run needs, simulate every transition, a zero test by an honest test of level `L`, then drain).

**`aacc_iff_cacc`**: `AAcc P L s0 g ↔ CAcc P (B L) s0 g`.
-/

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

/-- The marking during the simulation of the machine with counters `v` and `z` zero tests left. -/
def Mm (L : ℕ) (v : Bool → ℕ) (z : ℕ) : Mk :=
  Rb L + (B L - v false) • δ (.side L false false) + v false • δ (.side L false true) +
    (B L - v true) • δ (.side L true false) + v true • δ (.side L true true) + Bd L z

/-- Pointwise proof that the consumed tokens are available. -/
macro "dl_le" : tactic => `(tactic| (
  intro p
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, δ_apply, smul_eq_mul,
    List.count_cons, List.count_nil, beq_iff_eq]
  rcases p with ⟨k', r', b'⟩ | k' | k' <;> (try cases r') <;> (try cases b') <;> simp <;>
    (try split_ifs) <;> omega))

section main

variable {P : CM Q Φ} {L : ℕ}

theorem main_nop {t : CTr Q Φ} (ht : t ∈ P.trs) (hto : t.op = .nop) {S : Finset Φ}
    (hpre : ∀ f ∈ t.pre, f ∈ S) (v : Bool → ℕ) (z : ℕ) :
    AStep P L (.main t.src, S, Mm L v z) (.main t.dst, upd S t.add t.del, Mm L v z) :=
  astep_of (IsRule.mNop t ht hto) hpre (fun p => by simp) (mv_nn _) rfl

theorem main_inc {t : CTr Q Φ} (ht : t ∈ P.trs) {r : Bool} (hto : t.op = .inc r)
    {S : Finset Φ} (hpre : ∀ f ∈ t.pre, f ∈ S) {v : Bool → ℕ} (hb : v r + 1 ≤ B L) (z : ℕ) :
    AStep P L (.main t.src, S, Mm L v z)
      (.main t.dst, upd S t.add t.del, Mm L (Function.update v r (v r + 1)) z) := by
  refine astep_of (IsRule.mInc t ht r hto) hpre ?_ ?_ rfl
  · simp only [Mm, Bd]; cases r <;> dl_le
  · simp only [Mm, Bd]; cases r <;> mk_eq

theorem main_dec {t : CTr Q Φ} (ht : t ∈ P.trs) {r : Bool} (hto : t.op = .dec r)
    {S : Finset Φ} (hpre : ∀ f ∈ t.pre, f ∈ S) {v : Bool → ℕ} (h1 : 1 ≤ v r)
    (hb : v r ≤ B L) (z : ℕ) :
    AStep P L (.main t.src, S, Mm L v z)
      (.main t.dst, upd S t.add t.del, Mm L (Function.update v r (v r - 1)) z) := by
  refine astep_of (IsRule.mDec t ht r hto) hpre ?_ ?_ rfl
  · simp only [Mm, Bd]; cases r <;> dl_le
  · simp only [Mm, Bd]; cases r <;> mk_eq

theorem main_zero {t : CTr Q Φ} {i : ℕ} (hi : P.trs[i]? = some t) {r : Bool}
    (hto : t.op = .zero r) {S : Finset Φ} (hpre : ∀ f ∈ t.pre, f ∈ S) {v : Bool → ℕ}
    (h0 : v r = 0) (z : ℕ) :
    Reach P L (.main t.src, S, Mm L v (z + 1)) (.main t.dst, upd S t.add t.del, Mm L v z) := by
  have h1 := astep_of (S := S) (IsRule.mZ (P := P) (L := L) i t hi r hto) hpre
    (m := Mm L v (z + 1)) (m' := Mm L v z + (2 * B L) • δ (.c L))
    (by simp only [Mm, Bd]; dl_le) (by simp only [Mm, Bd]; mk_eq') (upd_nil S)
  have h2 := reach_frame (test_run (P := P) (L := L) (S := S) (.m i r) L r true rfl rfl rfl
      (B L))
    (m0 := Rb L + (B L - v (!r)) • δ (.side L (!r) false) + v (!r) • δ (.side L (!r) true) +
      Bd L z)
    (m := Mm L v z + (2 * B L) • δ (.c L)) (m' := Mm L v z)
    (by simp only [Mm, Bd]; cases r <;> mk_eq)
    (by simp only [Mm, Bd]; cases r <;> mk_eq)
  have h3 := astep_of (S := S) (IsRule.mExit (P := P) (L := L) i t hi r hto)
    (m := Mm L v z) (fun f hf => by simp at hf) (fun p => by simp) (mv_nn _) rfl
  exact (h2.head h1).tail h3

theorem main_step {q q' : Q} {S S' : Finset Φ} {v v' : Bool → ℕ}
    (h : CStepB P (B L) (q, S, v) (q', S', v')) (hv : ∀ r, v r ≤ B L) :
    ∃ e, ∀ z, Reach P L (.main q, S, Mm L v (z + e)) (.main q', S', Mm L v' z) := by
  obtain ⟨hs, hb⟩ := h
  dsimp only at hb
  cases hs with
  | mk t ht S0 v0 v0' hpre hop =>
    rcases hto : t.op with _ | r | r | r <;> rw [hto] at hop
    · subst hop; exact ⟨0, fun z => .single (main_nop ht hto hpre _ z)⟩
    · subst hop
      have := hb r
      simp at this
      exact ⟨0, fun z => .single (main_inc ht hto hpre this z)⟩
    · obtain ⟨h1, rfl⟩ := hop
      exact ⟨0, fun z => .single (main_dec ht hto hpre h1 (hv r) z)⟩
    · obtain ⟨h0, rfl⟩ := hop
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ht
      exact ⟨1, fun z => main_zero hi hto hpre h0 z⟩

/-- **The simulation of a bounded run of the counter machine.** -/
theorem main_run {c c' : CCfg Q Φ} (h : Relation.ReflTransGen (CStepB P (B L)) c c') :
    (∀ r, c.2.2 r ≤ B L) → ∃ n, ∀ z,
      Reach P L (.main c.1, c.2.1, Mm L c.2.2 (z + n)) (.main c'.1, c'.2.1, Mm L c'.2.2 z) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact ⟨0, fun z => .refl⟩
  | @head a b hab _ ih =>
    intro hc
    obtain ⟨n, hn⟩ := ih hab.2
    obtain ⟨e, he⟩ := main_step hab hc
    refine ⟨n + e, fun z => ?_⟩
    have := he (z + n)
    rw [show z + n + e = z + (n + e) by omega] at this
    exact this.trans (hn z)

end main

section drain

variable {P : CM Q Φ} {L : ℕ} {S : Finset Φ}

theorem drain_place {k : ℕ} (hk : k ≤ L) (r : Bool) : ∀ (n : ℕ) (m0 : Mk),
    Reach P L (.drain, S, n • δ (.side k r false) + m0) (.drain, S, m0) := by
  intro n
  induction n with
  | zero => intro m0; apply reach_of_eq; simp
  | succ n ih =>
    intro m0
    refine (Relation.ReflTransGen.single (astep0 (IsRule.drain k r hk)
      (m' := n • δ (.side k r false) + m0) ?_ ?_)).trans (ih m0)
    · cases r <;> dl_le
    · cases r <;> mk_eq

theorem drain_lv {k : ℕ} (hk : k ≤ L) (m0 : Mk) :
    Reach P L (.drain, S, Lv k + m0) (.drain, S, m0) := by
  rw [Lv, add_assoc]; exact (drain_place hk false _ _).trans (drain_place hk true _ _)

theorem drain_all : ∀ k ≤ L, ∀ m0 : Mk,
    Reach P L (.drain, S, Rr k + m0) (.drain, S, m0) := by
  intro k
  induction k with
  | zero =>
    intro hk m0
    rw [Rr_eq, add_comm (Rb _), add_assoc]
    refine (drain_lv hk _).trans (reach_of_eq ?_)
    simp [Rb]
  | succ k ih =>
    intro hk m0
    rw [Rr_eq, add_comm (Rb _), add_assoc]
    refine (drain_lv hk _).trans ?_
    rw [Rb_succ]; exact ih (by omega) m0

end drain

/-- **Completeness of the amplifier.** -/
theorem complete {P : CM Q Φ} {L : ℕ} {s0 : Finset Φ} {g : List Φ} (h : CAcc P (B L) s0 g) :
    AAcc P L s0 g := by
  obtain ⟨S, hrun, hg⟩ := h
  obtain ⟨n, hn⟩ := main_run (L := L) hrun (fun _ => Nat.zero_le _)
  refine ⟨S, ?_, hg⟩
  have h1 := setup_run (P := P) (L := L) (S := s0) n
  have h2 := astep0 (S := s0) (IsRule.blMain (P := P) (L := L)) (m := Rr L + Bd L n)
    (m' := Mm L (fun _ => 0) (0 + n)) (fun p => by simp)
    (by rw [mv_nn, Rr_eq]; simp only [Mm, Lv, Bd]; mk_eq)
  have h3 := hn 0
  have h4 := astep0 (S := S) (IsRule.toDrain (P := P) (L := L)) (m := Mm L (fun _ => 0) 0)
    (m' := Rr L + 0) (fun p => by simp)
    (by rw [mv_nn, Rr_eq]; simp only [Mm, Lv, Bd]; mk_eq)
  have h5 := drain_all (P := P) (L := L) (S := S) L le_rfl 0
  have h6 := astep0 (S := S) (IsRule.toDone (P := P) (L := L)) (m := 0) (m' := 0)
    (fun p => by simp) (mv_nn _)
  exact ((((h1.tail h2).trans h3).tail h4).trans h5).tail h6

/-- **The amplifier theorem**: the vector addition system accepts exactly when the counter
machine accepts with counters bounded by `B L = 2 ^ (2 ^ L)`. -/
theorem aacc_iff_cacc {P : CM Q Φ} {L : ℕ} {s0 : Finset Φ} {g : List Φ} :
    AAcc P L s0 g ↔ CAcc P (B L) s0 g :=
  ⟨sound, complete⟩


end Amp

end HTN
