import FondHtn.HardTR.Round
/-!
# CB22 Thm 5, P1 (abstract part): the refinement language is accepted by the thread automaton

The task hierarchy of the encoding (`doc/notes_cb22_thm5_progress2.md`, §2 "P1/P2"):

`main → loop A ∥ loop B ∥ finT`, `loop p → [block p, loop p] | []`,
`block p → tree p m ∥ reT p`, `tree p (k+1) → tree p k ∥ tree p k`, `tree p 0 → [bit p 0]`,
`bit p k → [wb p k b, bit p (k+1), rbT p k b]` (`k < m`), `bit p m → [core p]`,
`core p → [op p o, incT p, rvT p (opW o)] | [nrd p, op p o, incT p, rvT p (opW o)]`,
`incT p → [inc p k] | [wrap p]`, `rvT p γ → [rv p γ] | [dr p]`,
`rbT p k b → [rb p k b] | [dr p]`, `reT p → [rend p e] | [dr p]`, `finT → [fin]`.

`FOND.HardTR.TL.Gen M X u` is the (over-approximating) grammar of these tasks: sequences are
concatenated, parallel compositions interleaved (`HTN.Interleave`).

**`FOND.HardTR.TL.Mach.gen_main_acc`**: every word of `main` is accepted by the configuration
automaton `M.lts` from `C₀ = ⟨0, 0, finish pending⟩` (`FOND.HardTR.TL.Mach.C₀`).
The proof: each word thread runs through the thread automaton `Mach.thStep` (`TRun`), the
threads of a block run in the multiset (`MRun`, interleavings of thread runs), the blocks of a
loop run one after the other (`LRun`, via `stepC`), and the two loops and the finish action run
in the product (`Path`).
-/

namespace FOND

namespace HardTR

namespace TL

open HTN

/-- The tasks of the encoding. -/
inductive Nt
  | main
  | loop (p : Bool)
  | block (p : Bool)
  | tree (p : Bool) (k : ℕ)
  | bit (p : Bool) (k : ℕ)
  | core (p : Bool)
  | incT (p : Bool)
  | rvT (p γ : Bool)
  | rbT (p : Bool) (k : ℕ) (b : Bool)
  | reT (p : Bool)
  | finT

variable {G Op En : Type} (M : Mach G Op En)

/-- **The grammar of the task hierarchy.** -/
inductive Gen : Nt → List (Act Op En) → Prop
  | main {u v uv z} : Gen (.loop true) u → Gen (.loop false) v → Interleave u v uv →
      Interleave uv [.fin] z → Gen .main z
  | loopNil (p : Bool) : Gen (.loop p) []
  | loopCons {p u v} : Gen (.block p) u → Gen (.loop p) v → Gen (.loop p) (u ++ v)
  | block {p u v z} : Gen (.tree p M.m) u → Gen (.reT p) v → Interleave u v z → Gen (.block p) z
  | treeS {p k u v z} : Gen (.tree p k) u → Gen (.tree p k) v → Interleave u v z →
      Gen (.tree p (k + 1)) z
  | tree0 {p u} : Gen (.bit p 0) u → Gen (.tree p 0) u
  | bitS {p k u v} (b : Bool) : k < M.m → Gen (.bit p (k + 1)) u → Gen (.rbT p k b) v →
      Gen (.bit p k) (.wb p k b :: (u ++ v))
  | bitM {p u} : Gen (.core p) u → Gen (.bit p M.m) u
  | core {p u v} (o : Op) : Gen (.incT p) u → Gen (.rvT p (M.opW o)) v →
      Gen (.core p) (.op p o :: (u ++ v))
  | coreN {p u v} (o : Op) : Gen (.incT p) u → Gen (.rvT p (M.opW o)) v →
      Gen (.core p) (.nrd p :: .op p o :: (u ++ v))
  | inc (p : Bool) (k : ℕ) : Gen (.incT p) [.inc p k]
  | wrap (p : Bool) : Gen (.incT p) [.wrap p]
  | rv (p γ : Bool) : Gen (.rvT p γ) [.rv p γ]
  | rvD (p γ : Bool) : Gen (.rvT p γ) [.dr p]
  | rb (p : Bool) (k : ℕ) (b : Bool) : Gen (.rbT p k b) [.rb p k b]
  | rbD (p : Bool) (k : ℕ) (b : Bool) : Gen (.rbT p k b) [.dr p]
  | re (p : Bool) (e : En) : Gen (.reT p) [.rend p e]
  | reD (p : Bool) : Gen (.reT p) [.dr p]
  | fin : Gen .finT [.fin]

namespace Mach

/-! ## Runs -/

/-- A run of one thread (all actions of loop `p`). -/
inductive TRun (p : Bool) : Option Th → List (Act Op En) → Option Th → Prop
  | nil (q : Option Th) : TRun p q [] q
  | cons {q : Th} {a : Act Op En} {r r' : Option Th} {u : List (Act Op En)} :
      a.ap = some p → M.thStep q a r → TRun p r u r' → TRun p (some q) (a :: u) r'

/-- A run of a multiset of threads (all actions of loop `p`). -/
inductive MRun (p : Bool) : Multiset Th → List (Act Op En) → Multiset Th → Prop
  | nil (S : Multiset Th) : MRun p S [] S
  | cons {S S₁ S' : Multiset Th} {a : Act Op En} {u : List (Act Op En)} :
      a.ap = some p → M.stepT S a S₁ → MRun p S₁ u S' → MRun p S (a :: u) S'

/-- A run of a loop (blocks one after the other). -/
inductive LRun (p : Bool) : Multiset Th → List (Act Op En) → Multiset Th → Prop
  | nil (S : Multiset Th) : LRun p S [] S
  | cons {S S₁ S' : Multiset Th} {a : Act Op En} {u : List (Act Op En)} :
      a.ap = some p → M.stepC S a S₁ → LRun p S₁ u S' → LRun p S (a :: u) S'

/-- A run of the configuration automaton. -/
inductive Path : Cfg → List (Act Op En) → Cfg → Prop
  | nil (C : Cfg) : Path C [] C
  | cons {C C₁ C' : Cfg} {a : Act Op En} {u : List (Act Op En)} :
      M.cstep C a C₁ → Path C₁ u C' → Path C (a :: u) C'

variable {M}

theorem TRun.append {p : Bool} {q r r' : Option Th} {u v : List (Act Op En)}
    (h : M.TRun p q u r) (h' : M.TRun p r v r') : M.TRun p q (u ++ v) r' := by
  induction h with
  | nil => exact h'
  | cons ha hs _ ih => exact .cons ha hs (ih h')

theorem LRun.append {p : Bool} {S S₁ S' : Multiset Th} {u v : List (Act Op En)}
    (h : M.LRun p S u S₁) (h' : M.LRun p S₁ v S') : M.LRun p S (u ++ v) S' := by
  induction h with
  | nil => exact h'
  | cons ha hs _ ih => exact .cons ha hs (ih h')

theorem stepT_add {S S₁ T : Multiset Th} {a : Act Op En} (h : M.stepT S a S₁) :
    M.stepT (S + T) a (S₁ + T) := by
  obtain ⟨q, hq, r, hs, rfl⟩ := h
  refine ⟨q, Multiset.mem_add.2 (Or.inl hq), r, hs, ?_⟩
  rw [Multiset.erase_add_left_pos _ hq]
  abel

/-- A thread run inside a multiset. -/
theorem TRun.mrun {p : Bool} {q r : Option Th} {u : List (Act Op En)} (h : M.TRun p q u r)
    (T : Multiset Th) : M.MRun p (optM q + T) u (optM r + T) := by
  induction h with
  | nil => exact .nil _
  | @cons q a r r' u ha hs _ ih =>
    refine .cons ha ⟨q, by simp [optM], r, hs, ?_⟩ ih
    simp [optM]; abel

/-- **Interleavings of multiset runs.** -/
theorem MRun.interleave {p : Bool} {u v z : List (Act Op En)} (hz : Interleave u v z) :
    ∀ {S T S' T' : Multiset Th}, M.MRun p S u S' → M.MRun p T v T' →
      M.MRun p (S + T) z (S' + T') := by
  induction hz with
  | nil =>
    intro S T S' T' h1 h2
    cases h1; cases h2; exact .nil _
  | left a _ ih =>
    intro S T S' T' h1 h2
    cases h1 with
    | cons ha hs h1 => exact .cons ha (stepT_add hs) (ih h1 h2)
  | right a _ ih =>
    intro S T S' T' h1 h2
    cases h2 with
    | cons ha hs h2 =>
      refine .cons ha ?_ (by simpa [add_comm] using ih (T := _) h1 h2)
      simpa [add_comm] using stepT_add (T := S) hs

/-- Multiset runs are loop runs (the loop is busy). -/
theorem MRun.lrun {p : Bool} {S S' : Multiset Th} {u : List (Act Op En)} (h : M.MRun p S u S') :
    M.LRun p S u S' := by
  induction h with
  | nil => exact .nil _
  | cons ha hs _ ih => exact .cons ha (Or.inl hs) ih

/-- A block run from the empty loop. -/
theorem MRun.lrun_block {p : Bool} {S S' : Multiset Th} {u : List (Act Op En)}
    (h : M.MRun p S u S') (hS : S = M.block) (hS' : S' = 0) (hne : M.block ≠ 0) :
    M.LRun p 0 u S' := by
  cases h with
  | nil => exact absurd (hS.symm.trans hS') hne
  | cons ha hs h => subst hS; exact .cons ha (Or.inr ⟨rfl, hs⟩) h.lrun

/-- The configuration with loop multisets `S` (loop `true`), `T` (loop `false`). -/
def cmk (S T : Multiset Th) (f : Bool) : Cfg := ⟨fun q => if q then S else T, f⟩

theorem cstep_true {S S₁ T : Multiset Th} {f : Bool} {a : Act Op En} (ha : a.ap = some true)
    (h : M.stepC S a S₁) : M.cstep (cmk S T f) a (cmk S₁ T f) := by
  unfold cstep; rw [ha]; exact ⟨h, rfl, rfl⟩

theorem cstep_false {S T T₁ : Multiset Th} {f : Bool} {a : Act Op En} (ha : a.ap = some false)
    (h : M.stepC T a T₁) : M.cstep (cmk S T f) a (cmk S T₁ f) := by
  unfold cstep; rw [ha]; exact ⟨h, rfl, rfl⟩

theorem cstep_fin {S T : Multiset Th} : M.cstep (cmk S T true) .fin (cmk S T false) := by
  unfold cstep; exact ⟨rfl, rfl, rfl⟩

/-- A run of the second loop together with the finish thread. -/
inductive R23 : Multiset Th × Bool → List (Act Op En) → Multiset Th × Bool → Prop
  | nil (x : Multiset Th × Bool) : R23 x [] x
  | loop {T T₁ : Multiset Th} {f : Bool} {a : Act Op En} {u : List (Act Op En)} {y} :
      a.ap = some false → M.stepC T a T₁ → R23 (T₁, f) u y → R23 (T, f) (a :: u) y
  | fin {T : Multiset Th} {u : List (Act Op En)} {y} : R23 (T, false) u y → R23 (T, true) (.fin :: u) y

theorem LRun.r23 {T T' : Multiset Th} {u : List (Act Op En)} (h : M.LRun false T u T') (f : Bool) :
    M.R23 (T, f) u (T', f) := by
  induction h with
  | nil => exact .nil _
  | cons ha hs _ ih => exact .loop ha hs ih

theorem r23_of_interleave {v y : List (Act Op En)} (hz : Interleave v [.fin] y) :
    ∀ {T T' : Multiset Th}, M.LRun false T v T' → M.R23 (T, true) y (T', false) := by
  generalize hw : ([.fin] : List (Act Op En)) = w at hz
  induction hz with
  | nil => simp at hw
  | left a _ ih =>
    intro T T' h
    cases h with
    | cons ha hs h => exact .loop ha hs (ih hw h)
  | right a hz _ =>
    intro T T' h
    simp only [List.cons.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rw [hz.eq_of_nil_right]
    exact .fin (h.r23 false)

theorem path_of_interleave {u y z : List (Act Op En)} (hz : Interleave u y z) :
    ∀ {S S' : Multiset Th} {x x' : Multiset Th × Bool}, M.LRun true S u S' → M.R23 x y x' →
      M.Path (cmk S x.1 x.2) z (cmk S' x'.1 x'.2) := by
  induction hz with
  | nil =>
    intro S S' x x' h1 h2
    cases h1; cases h2; exact .nil _
  | left a _ ih =>
    intro S S' x x' h1 h2
    cases h1 with
    | cons ha hs h1 => exact .cons (cstep_true ha hs) (ih h1 h2)
  | right a _ ih =>
    intro S S' x x' h1 h2
    cases h2 with
    | loop ha hs h2 => exact .cons (cstep_false ha hs) (ih h1 h2)
    | fin h2 => exact .cons cstep_fin (ih h1 h2)

theorem Path.acc {C C' : Cfg} {u : List (Act Op En)} (h : M.Path C u C') (hC : M.lts.acc C') :
    M.lts.Acc C u := by
  induction h with
  | nil => exact .nil hC
  | cons hs _ ih => exact .cons hs (ih hC)

/-! ## The claims -/

theorem block_eq : M.block = M.W • {Th.hd 0 0} + {Th.re} := by
  unfold block fm
  rw [List.range_succ, List.filterMap_append]
  have : (List.range M.W).filterMap (M.wF (fun _ => false) 0) =
      List.replicate M.W (Th.hd 0 0) := by
    rw [List.filterMap_congr (g := fun _ => some (Th.hd 0 0))
      (fun i hi => by simp [wF, List.mem_range.1 hi])]
    simp
  rw [this]
  simp [wF, Multiset.nsmul_singleton]
  rw [← Multiset.coe_add, Multiset.coe_replicate]; rfl

theorem block_ne : M.block ≠ 0 := by
  rw [block_eq]; simp

/-- The claim of each task. -/
def Claim (M : Mach G Op En) : Nt → List (Act Op En) → Prop
  | .main, u => M.lts.Acc ⟨fun _ => 0, true⟩ u
  | .loop p, u => M.LRun p 0 u 0
  | .block p, u => M.MRun p M.block u 0
  | .tree p k, u => M.MRun p (2 ^ k • {Th.hd 0 0}) u 0
  | .bit p k, u => k ≤ M.m → ∀ a < 2 ^ k, ∃ A < 2 ^ M.m, A % 2 ^ k = a ∧
      M.TRun p (some (.hd k a)) u (tbNext k A)
  | .core p, u => ∀ a, M.TRun p (some (.hd M.m a)) u (some (.tb (M.m - 1) a))
  | .incT p, u => ∀ a γ, M.TRun p (some (.ic a γ)) u (some (.tv a γ))
  | .rvT p γ, u => ∀ a, M.TRun p (some (.tv a γ)) u (some (.tb (M.m - 1) a))
  | .rbT p k b, u => ∀ a, a.testBit k = b → M.TRun p (some (.tb k a)) u (tbNext k a)
  | .reT p, u => M.TRun p (some .re) u none
  | .finT, u => u = [.fin]

theorem single {p : Bool} {q : Th} {a : Act Op En} {r : Option Th} (ha : a.ap = some p)
    (h : M.thStep q a r) : M.TRun p (some q) [a] r := .cons ha h (.nil _)

/-- **Every word of the grammar satisfies the claim of its task.** -/
theorem gen_claim (hm : 0 < M.m) {X : Nt} {u : List (Act Op En)} (h : Gen M X u) :
    M.Claim X u := by
  induction h with
  | main _ _ huv hz ih1 ih2 =>
    obtain ⟨y, hy, hz'⟩ := huv.assoc hz
    have hp := path_of_interleave hz' ih1 (r23_of_interleave hy ih2)
    have e : cmk 0 0 true = ⟨fun _ => 0, true⟩ := by
      unfold cmk; congr 1; funext q; cases q <;> rfl
    show M.lts.Acc _ _
    rw [← e]
    exact hp.acc (by refine ⟨?_, ?_, ?_⟩ <;> simp [cmk])
  | loopNil p => exact .nil _
  | loopCons _ _ ih1 ih2 => exact (ih1.lrun_block rfl rfl block_ne).append ih2
  | block _ _ hz ih1 ih2 =>
    have h2 := ih2.mrun 0
    simp only [optM, Option.toList_some, Option.toList_none, Multiset.coe_singleton,
      Multiset.coe_nil, add_zero] at h2
    show M.MRun _ M.block _ 0
    rw [block_eq]
    simpa using MRun.interleave hz ih1 h2
  | treeS _ _ hz ih1 ih2 =>
    rw [Claim, pow_succ, mul_two, add_nsmul]
    simpa using MRun.interleave hz ih1 ih2
  | tree0 _ ih =>
    obtain ⟨A, -, -, hr⟩ := ih (Nat.zero_le _) 0 (by norm_num)
    have := hr.mrun 0
    simpa [tbNext, optM] using this
  | @bitS p k u v b hk _ _ ih1 ih2 =>
    intro _ a ha
    obtain ⟨A, hA, hAk, hr⟩ := ih1 (by omega) (a + if b then 2 ^ k else 0)
      (by rw [pow_succ]; split_ifs <;> omega)
    have hbit : A.testBit k = b := by
      have h1 := mod_two_pow_succ' A k
      have h2 : A % 2 ^ k = a := by
        rw [← Nat.mod_mod_of_dvd A (pow_dvd_pow 2 (Nat.le_succ k)), hAk]
        split_ifs <;> simp [Nat.mod_eq_of_lt ha]
      rw [hAk, h2] at h1
      cases b <;> cases hb : A.testBit k <;> simp_all <;> omega
    refine ⟨A, hA, ?_, ?_⟩
    · rw [← Nat.mod_mod_of_dvd A (pow_dvd_pow 2 (Nat.le_succ k)), hAk]
      split_ifs <;> simp [Nat.mod_eq_of_lt ha]
    · refine .cons rfl ⟨rfl, hk, rfl⟩ (hr.append ?_)
      simp only [tbNext, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] 
      exact ih2 A hbit
  | bitM _ ih =>
    intro _ a ha
    refine ⟨a, ha, Nat.mod_eq_of_lt ha, ?_⟩
    simpa [tbNext, Nat.pos_iff_ne_zero.1 hm] using ih a
  | core o _ _ ih1 ih2 =>
    intro a
    exact .cons rfl ⟨rfl, rfl⟩ ((ih1 a _).append (ih2 a))
  | coreN o _ _ ih1 ih2 =>
    intro a
    exact .cons rfl ⟨rfl, rfl⟩ (.cons rfl rfl ((ih1 a _).append (ih2 a)))
  | inc p k => intro a γ; exact single rfl rfl
  | wrap p => intro a γ; exact single rfl rfl
  | rv p γ => intro a; exact single rfl ⟨rfl, rfl⟩
  | rvD p γ => intro a; exact single rfl rfl
  | rb p k b => intro a ha; exact single rfl ⟨rfl, ha.symm, rfl⟩
  | rbD p k b => intro a _; exact single rfl rfl
  | re p e => exact single rfl rfl
  | reD p => exact single rfl rfl
  | fin => rfl

/-- **The words of `main` are accepted by the configuration automaton.** -/
theorem gen_main_acc (hm : 0 < M.m) {u : List (Act Op En)} (h : Gen M .main u) :
    M.lts.Acc ⟨fun _ => 0, true⟩ u :=
  gen_claim hm h

end Mach

end TL

end HardTR

end FOND
