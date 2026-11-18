import ComplexityTheory.TOtoHD.Amp.Defs
/-!
# The amplifier: invariants and potentials

* `E` is the expected sum of every pair at a control state: `B k` for the pairs already filled,
  `0` for the pairs not yet filled, and the progress of the current multiplication loop for the
  pair being filled.
* `prg` is the number of tokens the current multiplication loop has produced so far, provided
  every zero test of the level below was honest (expressed through the loop counters).
* `Inv K` collects what holds at every reachable configuration once every zero test of a level
  below `K` was honest: the sums of the pairs of the levels `≤ K`, which `true` sides are empty,
  and the facts.
* `Psi K` is the potential of level `K`: the move budget, minus `2 B K` per test budget, plus what
  the current budget round still owes, minus what the current test of level `K` can still move.
  It never decreases, and it stays constant exactly when every test of level `K` is honest.
-/

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

/-- **The progress of the current multiplication loop**, in terms of its loop counters (the
`true` sides of the pairs of level `k`; meaningful when the tests of level `k` are honest). -/
def prg : Loc Q → Mk → ℕ
  | .sp k _ .inner, m => m (.side k false true) * B k + m (.side k true true)
  | .sp k _ .restj, m => m (.side k false true) * B k + B k
  | .sp k _ .outer, m => m (.side k false true) * B k
  | .sp k _ .resti, _ => B k * B k
  | .zt (.sj k _ _) _, m => m (.side k false true) * B k + B k
  | .zt (.si k _ _) _, _ => B k * B k
  | _, _ => 0

/-- The expected sum of the pair `r` of level `k` during the multiplication loop over the
counters of level `k0` at site `s`, whose progress is `π`. -/
def Esp (k0 : ℕ) (s : Site) (π k : ℕ) (r : Bool) : ℕ :=
  if k ≤ k0 then B k else if k0 + 1 < k then 0 else
    match s with
    | .comp r0 => if r = r0 then π else if r0 then B k else 0
    | .bud _ => B k

/-- **The expected sum of the pair `r` of level `k`** at a control state. -/
def E (l : Loc Q) (m : Mk) (k : ℕ) (r : Bool) : ℕ :=
  match l with
  | .start => 0
  | .bl k0 => if k ≤ k0 then B k else 0
  | .sp k0 s _ => Esp k0 s (prg l m) k r
  | .zt (.sj k0 s _) _ => Esp k0 s (prg l m) k r
  | .zt (.si k0 s _) _ => Esp k0 s (prg l m) k r
  | _ => B k

/-- The control states before the simulation of the machine. -/
def Pre : Loc Q → Prop
  | .start => True
  | .bl _ => True
  | .sp _ _ _ => True
  | .zt (.sj _ _ _) _ => True
  | .zt (.si _ _ _) _ => True
  | _ => False

/-- The control states before draining. -/
def NotDr : Loc Q → Prop
  | .drain => False
  | .done => False
  | _ => True

/-- The control states at which the inner loop counter of level `k` may be away from rest. -/
def InJ (k : ℕ) : Loc Q → Prop
  | .sp k' _ .inner => k' = k
  | .sp k' _ .restj => k' = k
  | .zt (.sj k' _ _) _ => k' = k
  | _ => False

/-- The control states at which the outer loop counter of level `k` may be away from rest. -/
def InI (k : ℕ) : Loc Q → Prop
  | .sp k' _ _ => k' = k
  | .zt (.sj k' _ _) _ => k' = k
  | .zt (.si k' _ _) _ => k' = k
  | _ => False

/-- The control states that exist. -/
def Valid (P : CM Q Φ) (L : ℕ) : Loc Q → Prop
  | .bl k => k ≤ L
  | .sp k _ _ => k < L
  | .zt (.sj k _ _) _ => k < L
  | .zt (.si k _ _) _ => k < L
  | .zt (.m i r) _ => ∃ t, P.trs[i]? = some t ∧ t.op = .zero r
  | _ => True

/-- **The invariant up to level `K`.** -/
structure Inv (P : CM Q Φ) (L K : ℕ) (s0 : Finset Φ) (x : ACfg Q Φ) : Prop where
  valid : Valid P L x.1
  facts : Pre x.1 → x.2.1 = s0
  sum : ∀ k ≤ K, ∀ r, NotDr x.1 →
    x.2.2 (.side k r false) + x.2.2 (.side k r true) = E x.1 x.2.2 k r
  zero : ∀ r, Pre x.1 → x.2.2 (.side L r true) = 0
  restJ : ∀ k < K, ¬ InJ k x.1 → x.2.2 (.side k true true) = 0
  restI : ∀ k < K, ¬ InI k x.1 → x.2.2 (.side k false true) = 0

/-- The multiplication loop a control state belongs to. -/
def spawnOf : Loc Q → Option (ℕ × Site)
  | .sp k s _ => some (k, s)
  | .zt (.sj k s _) _ => some (k, s)
  | .zt (.si k s _) _ => some (k, s)
  | _ => none

/-- What the current budget round of level `k` still owes. -/
def owed (k : ℕ) (l : Loc Q) (m : Mk) : ℤ :=
  match spawnOf l with
  | some (k', .bud false) => if k' + 1 = k then 2 * (B k : ℤ) - prg l m else 0
  | some (k', .bud true) => if k' + 1 = k then (B k : ℤ) - prg l m else 0
  | _ => 0

/-- What the current zero test of level `k` can still move, at most. -/
def Rz (L k : ℕ) : Loc Q → Mk → ℤ
  | .zt z .A, m => if z.lvl L = k then (m (.side k z.pr (!z.sd)) : ℤ) + B k else 0
  | .zt z .A', m => if z.lvl L = k then (m (.side k z.pr (!z.sd)) : ℤ) + B k - 1 else 0
  | .zt z .B, m => if z.lvl L = k then (m (.side k z.pr z.sd) : ℤ) else 0
  | .zt z .B', m => if z.lvl L = k then (m (.side k z.pr z.sd) : ℤ) - 1 else 0
  | _, _ => 0

/-- **The potential of level `k`.** -/
def Psi (L k : ℕ) (x : ACfg Q Φ) : ℤ :=
  (x.2.2 (.c k) : ℤ) - 2 * (B k : ℤ) * x.2.2 (.d k) + owed k x.1 x.2.2 - Rz L k x.1 x.2.2

/-- **Honesty of a step at level `k`**: entering a zero test of level `k` requires the tested side
to be empty, switching from the first to the second half requires the other side to be empty, and
leaving requires the tested side to be empty again. -/
def Hon (L k : ℕ) (x y : ACfg Q Φ) : Prop :=
  ∀ z : ZI, z.lvl L = k →
    ((y.1 = .zt z .A ∧ ∀ ph, x.1 ≠ .zt z ph) → x.2.2 (.side k z.pr z.sd) = 0) ∧
    ((x.1 = .zt z .A ∧ y.1 = .zt z .B) → x.2.2 (.side k z.pr (!z.sd)) = 0) ∧
    ((x.1 = .zt z .B ∧ ∀ ph, y.1 ≠ .zt z ph) → x.2.2 (.side k z.pr z.sd) = 0)

/-! ### A generic monotone-potential lemma -/

theorem rtg_pot {α : Type} {R : α → α → Prop} {I : α → Prop} {f : α → ℤ}
    (hstep : ∀ x y, R x y → I x → I y ∧ f x ≤ f y) {a b : α}
    (h : Relation.ReflTransGen R a b) (ha : I a) :
    I b ∧ f a ≤ f b ∧
      (f b ≤ f a → Relation.ReflTransGen (fun x y => R x y ∧ I x ∧ f x = f y) a b) := by
  induction h with
  | refl => exact ⟨ha, le_rfl, fun _ => .refl⟩
  | @tail y z _ hyz ih =>
    obtain ⟨hIy, hay, hrun⟩ := ih
    obtain ⟨hIz, hyz'⟩ := hstep y z hyz hIy
    refine ⟨hIz, hay.trans hyz', fun hle => ?_⟩
    have h1 : f y ≤ f a := hyz'.trans hle
    exact .tail (hrun h1) ⟨hyz, hIy, by omega⟩

/-- Restricting the steps of a run by a property of the steps that every step has. -/
theorem rtg_mono_and {α : Type} {R S : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) (hS : ∀ x y, R x y → S x y) :
    Relation.ReflTransGen (fun x y => R x y ∧ S x y) a b := by
  induction h with
  | refl => exact .refl
  | tail _ hyz ih => exact .tail ih ⟨hyz, hS _ _ hyz⟩

end Amp

end HTN
