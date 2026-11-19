import FondHtn.FairUndec.Desc
import FondHtn.HardTR.TLang
/-!
# The refinements of the description

**`FOND.FU.netYield_tnI`**: every refinement of the initial network is an interleaving of two
words `w₁ · aD` and `w₂ · aD`, where `wᵦ` runs the stack `b` down from its initial content
(`FOND.FU.RD`): each symbol is either popped by a transition of the stack, which pushes its word,
or drained.
-/

namespace FOND

namespace FU

open HTN HTN.Syn HTN.Article HTN.Undec AcycHard.Sav HardTR HardTR.TD

/-- **Run-downs of a stack**, with drains. -/
inductive RD (M : TSM) (b : Bool) : List ℕ → List ℕ → Prop
  | nil : RD M b [] []
  | step {n : ℕ} {rest w : List ℕ} (hn : n < M.trans.length) (hb : (tr M n).stk = b)
      (h : RD M b ((tr M n).push ++ rest) w) : RD M b ((tr M n).pop :: rest) (aT n :: w)
  | drain {a : ℕ} {rest w : List ℕ} (h : RD M b rest w) : RD M b (a :: rest) (aD :: w)

variable {M : TSM} {s₁ s₂ : List ℕ}

theorem seqY_append_iff {A C : Type} {Y : A ⊕ C → List A → Prop} :
    ∀ {xs ys : List (A ⊕ C)} {as : List A},
      SeqY Y (xs ++ ys) as ↔ ∃ u v, as = u ++ v ∧ SeqY Y xs u ∧ SeqY Y ys v
  | [], ys, as => by
    rw [List.nil_append]
    exact ⟨fun h => ⟨[], as, rfl, .nil, h⟩, fun ⟨u, v, he, hu, hv⟩ => by
      rw [seqY_nil_iff] at hu; subst hu; simpa [he] using hv⟩
  | x :: xs, ys, as => by
    rw [List.cons_append, seqY_cons_iff]
    constructor
    · rintro ⟨u, v, rfl, hu, hv⟩
      obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := seqY_append_iff.1 hv
      exact ⟨u ++ v₁, v₂, by simp, .cons hu h₁, h₂⟩
    · rintro ⟨u, v, rfl, hu, hv⟩
      rw [seqY_cons_iff] at hu
      obtain ⟨u₁, u₂, rfl, h₁, h₂⟩ := hu
      exact ⟨u₁, u₂ ++ v, by simp, h₁, seqY_append_iff.2 ⟨u₂, v, rfl, h₂, hv⟩⟩

theorem RD.append {b : Bool} {s s' w w' : List ℕ} (h : RD M b s w) (h' : RD M b s' w') :
    RD M b (s ++ s') (w ++ w') := by
  induction h with
  | nil => simpa using h'
  | step hn hb _ ih =>
    rw [List.cons_append, List.cons_append]
    exact .step hn hb (by rw [← List.append_assoc]; exact ih)
  | drain _ ih => exact .drain ih

/-- The letters of a run-down are declared actions. -/
theorem RD.mem {b : Bool} {s w : List ℕ} (h : RD M b s w) :
    ∀ x ∈ w, (∃ n < M.trans.length, x = aT n) ∨ x = aD := by
  induction h with
  | nil => simp
  | step hn _ _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl ⟨_, hn, rfl⟩
    · exact ih x hx
  | drain _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inr rfl
    · exact ih x hx

/-- The words of a compound task. -/
def WC (M : TSM) (s₁ s₂ : List ℕ) (c : ℕ) (as : List ℕ) : Prop :=
  (∀ b a, c = sym b a → RD M b [a] as) ∧ (∀ b, c = bot b → as = [aD]) ∧
    (∀ b, c = root b → ∃ w, RD M b (stk0 s₁ s₂ b) w ∧ as = w ++ [aD]) ∧
    (c = root0 → ∃ w₁ w₂, RD M false s₁ w₁ ∧ RD M true s₂ w₂ ∧ Interleave (w₁ ++ [aD]) (w₂ ++ [aD]) as)

variable {F : Type} {D : HTN.Domain F ℕ ℕ ℕ}

/-- The claim for refinements within `n` steps. -/
def QF (M : TSM) (s₁ s₂ : List ℕ) (D : HTN.Domain F ℕ ℕ ℕ) (n : ℕ) : Prop :=
  ∀ m ∈ D.methods, ∀ as, D.NetYieldN n m.subtasks as → WC M s₁ s₂ m.abstractTask as

theorem yl_sym {n : ℕ} (IH : ∀ k < n, QF M s₁ s₂ D k) {b : Bool} {a : ℕ} {u : List ℕ}
    (h : YL D n (Sum.inr (sym b a)) u) : RD M b [a] u := by
  rcases h with ⟨x, hx, -⟩ | ⟨c, k, m, hc, hk, hm, hmc, hy⟩
  · simp at hx
  · simp only [Sum.inr.injEq] at hc
    exact (IH k hk m hm _ hy).1 b a (by rw [hmc, hc])

theorem yl_bot {n : ℕ} (IH : ∀ k < n, QF M s₁ s₂ D k) {b : Bool} {u : List ℕ}
    (h : YL D n (Sum.inr (bot b)) u) : u = [aD] := by
  rcases h with ⟨x, hx, -⟩ | ⟨c, k, m, hc, hk, hm, hmc, hy⟩
  · simp at hx
  · simp only [Sum.inr.injEq] at hc
    exact (IH k hk m hm _ hy).2.1 b (by rw [hmc, hc])

theorem yl_root {n : ℕ} (IH : ∀ k < n, QF M s₁ s₂ D k) {b : Bool} {u : List ℕ}
    (h : YL D n (Sum.inr (root b)) u) : ∃ w, RD M b (stk0 s₁ s₂ b) w ∧ u = w ++ [aD] := by
  rcases h with ⟨x, hx, -⟩ | ⟨c, k, m, hc, hk, hm, hmc, hy⟩
  · simp at hx
  · simp only [Sum.inr.injEq] at hc
    exact (IH k hk m hm _ hy).2.2.1 b (by rw [hmc, hc])

theorem yl_root0 {n : ℕ} (IH : ∀ k < n, QF M s₁ s₂ D k) {u : List ℕ}
    (h : YL D n (Sum.inr root0) u) : ∃ w₁ w₂, RD M false s₁ w₁ ∧ RD M true s₂ w₂ ∧
      Interleave (w₁ ++ [aD]) (w₂ ++ [aD]) u := by
  rcases h with ⟨x, hx, -⟩ | ⟨c, k, m, hc, hk, hm, hmc, hy⟩
  · simp at hx
  · simp only [Sum.inr.injEq] at hc
    exact (IH k hk m hm _ hy).2.2.2 (by rw [hmc, hc])

theorem seqY_symL {n : ℕ} (IH : ∀ k < n, QF M s₁ s₂ D k) {b : Bool} :
    ∀ (s : List ℕ) {as : List ℕ}, SeqY (YL D n) ((symL b s).map toLab) as → RD M b s as
  | [], as, h => by
    simp only [symL, List.map_nil, seqY_nil_iff] at h; subst h; exact .nil
  | a :: s, as, h => by
    simp only [symL, List.map_cons, seqY_cons_iff] at h
    obtain ⟨u, v, rfl, hu, hv⟩ := h
    have := (yl_sym IH (by simpa [toLab] using hu)).append (seqY_symL IH s hv)
    simpa using this

variable (hmwf : ∀ m ∈ D.methods, m.subtasks.WF)
include hmwf

set_option maxHeartbeats 1000000 in
/-- **Every method body refines into words of its task.** -/
theorem pm_allF {n : ℕ} (IH : ∀ k < n, QF M s₁ s₂ D k) :
    ∀ e ∈ meths M s₁ s₂, ∀ as, D.NetYieldN n e.2.toTaskNetwork as → WC M s₁ s₂ e.1 as := by
  intro e he as h
  simp only [meths, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with ((((⟨k, hk, rfl⟩ | ⟨b, -, a, -, rfl⟩) | ⟨b, -, rfl⟩) | ⟨b, -, rfl⟩) | rfl)
  · -- a transition
    have hy := seqY_desc hmwf h
    simp only [List.map_cons, seqY_cons_iff] at hy
    obtain ⟨u, v, rfl, hu, hv⟩ := hy
    have hu' : u = [aT k] := by
      rcases hu with ⟨x, hx, rfl⟩ | ⟨c, -, -, hc, -⟩
      · simp [toLab] at hx; rw [hx]
      · simp [toLab] at hc
    subst hu'
    have hrd := seqY_symL IH _ hv
    refine ⟨fun b a he => ?_, fun b he => absurd he (sym_ne_bot _ _ _),
      fun b he => absurd he (sym_ne_root _ _ _), fun he => absurd he (sym_ne_root0 _ _)⟩
    obtain ⟨rfl, rfl⟩ := sym_inj he.symm
    exact .step hk rfl (by simpa using hrd)
  · -- a drain of a symbol
    have hy := seqY_desc hmwf h
    simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at hy
    obtain ⟨u, v, rfl, hu, rfl⟩ := hy
    have hu' : u = [aD] := by
      rcases hu with ⟨x, hx, rfl⟩ | ⟨c, -, -, hc, -⟩
      · simp [toLab] at hx; rw [hx]
      · simp [toLab] at hc
    subst hu'
    refine ⟨fun b' a' he => ?_, fun b he => absurd he (sym_ne_bot _ _ _),
      fun b he => absurd he (sym_ne_root _ _ _), fun he => absurd he (sym_ne_root0 _ _)⟩
    obtain ⟨rfl, rfl⟩ := sym_inj he.symm
    exact .drain .nil
  · -- a bottom
    have hy := seqY_desc hmwf h
    simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at hy
    obtain ⟨u, v, rfl, hu, rfl⟩ := hy
    have hu' : u = [aD] := by
      rcases hu with ⟨x, hx, rfl⟩ | ⟨c, -, -, hc, -⟩
      · simp [toLab] at hx; rw [hx]
      · simp [toLab] at hc
    subst hu'
    refine ⟨fun b' a' he => absurd he.symm (sym_ne_bot _ _ _), fun b' he => by simp,
      fun b' he => absurd he (bot_ne_root _ _), fun he => absurd he (bot_ne_root0 _)⟩
  · -- a stack
    have hy := seqY_desc hmwf h
    rw [List.map_append, seqY_append_iff] at hy
    obtain ⟨u, v, rfl, hu, hv⟩ := hy
    simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at hv
    obtain ⟨x, y, rfl, hx, rfl⟩ := hv
    have hx' := yl_bot IH (by simpa [toLab] using hx)
    subst hx'
    refine ⟨fun b' a' he => absurd he.symm (sym_ne_root _ _ _), fun b' he => absurd he.symm (bot_ne_root _ _),
      fun b' he => ?_, fun he => absurd he (root_ne_root0 _)⟩
    obtain rfl := root_inj he.symm
    exact ⟨u, seqY_symL IH _ hu, by simp⟩
  · -- the root
    have hy := setY_desc hmwf h
    simp only [List.map_cons, List.map_nil, setY_cons_iff, setY_nil_iff] at hy
    obtain ⟨u, v, hu, ⟨w, z, hw, rfl, hi2⟩, hi⟩ := hy
    obtain rfl := hi2.eq_of_nil_right
    obtain ⟨w₁, h₁, rfl⟩ := yl_root IH (b := false) (by simpa [toLab] using hu)
    obtain ⟨w₂, h₂, rfl⟩ := yl_root IH (b := true) (by simpa [toLab] using hw)
    refine ⟨fun b' a' he => absurd he.symm (sym_ne_root0 _ _), fun b' he => absurd he.symm (bot_ne_root0 _),
      fun b' he => absurd he.symm (root_ne_root0 _), fun _ => ⟨w₁, w₂, h₁, h₂, hi⟩⟩

theorem qf_all (hD : D.methods = {m | ∃ e ∈ meths M s₁ s₂, e.toMethod = m}) : ∀ n, QF M s₁ s₂ D n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro m hm as hy
    rw [hD] at hm
    obtain ⟨e, he, rfl⟩ := hm
    exact pm_allF hmwf IH e he as hy

/-- **The refinements of the initial network.** -/
theorem netYield_tnI (hD : D.methods = {m | ∃ e ∈ meths M s₁ s₂, e.toMethod = m}) {as : List ℕ}
    (h : D.NetYield (seqTn [(true, root0)]).toTaskNetwork as) :
    ∃ w₁ w₂, RD M false s₁ w₁ ∧ RD M true s₂ w₂ ∧ Interleave (w₁ ++ [aD]) (w₂ ++ [aD]) as := by
  obtain ⟨n, hn⟩ := h
  have := seqY_desc hmwf hn
  simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at this
  obtain ⟨u, v, rfl, hu, rfl⟩ := this
  rw [List.append_nil]
  exact yl_root0 (fun k _ => qf_all hmwf hD k) (by simpa [toLab] using hu)

end FU

end FOND
