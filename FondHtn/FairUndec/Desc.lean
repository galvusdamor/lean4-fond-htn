import FondHtn.FairUndec.Det
import FondHtn.AcycHard.InstDesc
import FondHtn.Lang.Desc
/-!
# The FOND description of a two-stack machine with stop ticks

For a two-stack machine `M` and initial stacks `s₁, s₂` (`FOND.FU.desc`):

* **facts**: `fq q` (the control state is `q`) and `fStop` (nature has stopped the run);
* **actions**: for each transition `n`, the action `aT n` with precondition `fq (src n)`,
  negative precondition `fStop`, and two effects — move the control to `tgt n`, or set `fStop`
  (the *tick*); and the action `aD` (drain), with precondition `fStop` and no effect;
* **compound tasks**: `sym b a` (the symbol `a` on the stack `b`), `bot b` (the bottom of the
  stack `b`), `root b` (the stack `b`) and `root0`;
* **methods**: a transition `n` popping `a` from `b`: `sym b a → aT n · sym b w₁ ⋯ sym b w_k`
  (`w` pushed); drains `sym b a → aD`, `bot b → aD` for every symbol `a` of the machine;
  `root b → sym b s_b ⋯ · bot b`; `root0 → {root false, root true}` (unordered);
* **initial network** `root0`, **initial state** `{fq start}`.

The empty network is reachable only after a tick sets `fStop`; while `fStop` is unset, the
plan simulates the machine.
-/

namespace FOND

namespace FU

open HTN HTN.Syn HTN.Article HTN.Undec AcycHard.Sav

/-- The transition at a position. -/
def tr (M : TSM) (n : ℕ) : Tr := M.trans.getD n default

/-- The fact: the control state is `q`. -/
def fq (q : ℕ) : ℕ := 2 * q + 2
/-- The fact: stopped. -/
def fStop : ℕ := 1

/-- The action of the transition `n`. -/
def aT (n : ℕ) : ℕ := 2 * n + 1
/-- The drain action. -/
def aD : ℕ := 0

/-- The symbol `a` on the stack `b`. -/
def sym (b : Bool) (a : ℕ) : ℕ := Nat.pair 0 (Nat.pair b.toNat a)
/-- The bottom of the stack `b`. -/
def bot (b : Bool) : ℕ := Nat.pair 1 b.toNat
/-- The stack `b`. -/
def root (b : Bool) : ℕ := Nat.pair 2 b.toNat
/-- The root. -/
def root0 : ℕ := Nat.pair 3 0

/-- The labels of a stack content. -/
def symL (b : Bool) (s : List ℕ) : List (Bool × ℕ) := s.map fun a => (true, sym b a)

variable (M : TSM) (s₁ s₂ : List ℕ)

/-- The initial stack `b`. -/
def stk0 (b : Bool) : List ℕ := if b then s₂ else s₁

/-- The symbols of the machine and of the initial stacks. -/
def alph : List ℕ := s₁ ++ s₂ ++ M.trans.flatMap fun t => t.pop :: t.push

/-- The action description of a transition. -/
def actT (n : ℕ) : FActDesc :=
  (aT n, [fq (tr M n).src], [fStop], [([fq (tr M n).tgt], [fq (tr M n).src]), ([fStop], [])])

/-- The drain action description. -/
def actD : FActDesc := (aD, [fStop], [], [([], [])])

/-- The actions. -/
def acts : List FActDesc := (List.range M.trans.length).map (actT M) ++ [actD]

/-- The method of a transition. -/
def methT (n : ℕ) : MethodDesc :=
  (sym (tr M n).stk (tr M n).pop, seqTn ((false, aT n) :: symL (tr M n).stk (tr M n).push))

/-- The methods. -/
def meths : List MethodDesc :=
  (List.range M.trans.length).map (methT M) ++
    ([false, true].flatMap fun b => (alph M s₁ s₂).map fun a => (sym b a, seqTn [(false, aD)])) ++
    ([false, true].map fun b => (bot b, seqTn [(false, aD)])) ++
    ([false, true].map fun b => (root b, seqTn (symL b (stk0 s₁ s₂ b) ++ [(true, bot b)]))) ++
    [(root0, setTn [(true, root false), (true, root true)])]

/-- **The description.** -/
def desc : FProbDesc := ((acts M, meths M s₁ s₂), ([fq M.start], seqTn [(true, root0)]))

/-! ## Basic facts -/

theorem aT_inj {n n' : ℕ} (h : aT n = aT n') : n = n' := by unfold aT at h; omega

theorem aT_ne_aD (n : ℕ) : aT n ≠ aD := by unfold aT aD; omega

theorem fq_inj {q q' : ℕ} (h : fq q = fq q') : q = q' := by unfold fq at h; omega

theorem fq_ne_stop (q : ℕ) : fq q ≠ fStop := by unfold fq fStop; omega

theorem sym_inj {b b' : Bool} {a a' : ℕ} (h : sym b a = sym b' a') : b = b' ∧ a = a' := by
  simp only [sym, Nat.pair_eq_pair, true_and] at h
  refine ⟨?_, h.2⟩
  cases b <;> cases b' <;> simp_all

theorem sym_ne_bot (b b' : Bool) (a : ℕ) : sym b a ≠ bot b' := by simp [sym, bot, Nat.pair_eq_pair]
theorem sym_ne_root (b b' : Bool) (a : ℕ) : sym b a ≠ root b' := by simp [sym, root, Nat.pair_eq_pair]
theorem sym_ne_root0 (b : Bool) (a : ℕ) : sym b a ≠ root0 := by simp [sym, root0, Nat.pair_eq_pair]
theorem bot_inj {b b' : Bool} (h : bot b = bot b') : b = b' := by
  simp only [bot, Nat.pair_eq_pair, true_and] at h; cases b <;> cases b' <;> simp_all
theorem root_inj {b b' : Bool} (h : root b = root b') : b = b' := by
  simp only [root, Nat.pair_eq_pair, true_and] at h; cases b <;> cases b' <;> simp_all
theorem bot_ne_root (b b' : Bool) : bot b ≠ root b' := by simp [bot, root, Nat.pair_eq_pair]
theorem bot_ne_root0 (b : Bool) : bot b ≠ root0 := by simp [bot, root0, Nat.pair_eq_pair]
theorem root_ne_root0 (b : Bool) : root b ≠ root0 := by simp [root, root0, Nat.pair_eq_pair]

theorem mem_acts {a : FActDesc} : a ∈ acts M ↔ (∃ n < M.trans.length, a = actT M n) ∨ a = actD := by
  simp only [acts, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  constructor
  · rintro (⟨n, hn, rfl⟩ | rfl)
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨n, hn, rfl⟩ | rfl)
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr rfl

theorem declared_iff {x : ℕ} : (desc M s₁ s₂).Declared x ↔ (∃ n < M.trans.length, x = aT n) ∨ x = aD := by
  simp only [FProbDesc.Declared, desc, FProbDesc.actions, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases (mem_acts M).1 ha with ⟨n, hn, rfl⟩ | rfl
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨n, hn, rfl⟩ | rfl)
    · exact ⟨_, (mem_acts M).2 (Or.inl ⟨n, hn, rfl⟩), rfl⟩
    · exact ⟨_, (mem_acts M).2 (Or.inr rfl), rfl⟩

/-- **The description is well formed.** -/
theorem valid : (desc M s₁ s₂).Valid where
  names_nodup := by
    simp only [desc, FProbDesc.actions, acts, List.map_append, List.map_map, List.map_cons,
      List.map_nil]
    rw [List.nodup_append]
    refine ⟨?_, List.nodup_singleton _, ?_⟩
    · refine List.Nodup.map (fun n n' h => aT_inj h) List.nodup_range
    · intro x hx y hy
      simp only [List.mem_map, List.mem_range, Function.comp_apply, List.mem_singleton] at hx hy
      obtain ⟨n, -, rfl⟩ := hx
      subst hy
      exact aT_ne_aD n
  effs_ne := by
    intro a ha
    rcases (mem_acts M).1 ha with ⟨n, -, rfl⟩ | rfl <;> simp [actT, actD, FActDesc.effs]
  tnI := seqTn_valid fun q hq hf => by simp at hq; subst hq; simp at hf
  methods := by
    intro e he
    simp only [desc, FProbDesc.methods, meths, List.mem_append, List.mem_map, List.mem_range,
      List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with ((((⟨n, hn, rfl⟩ | ⟨b, -, a, -, rfl⟩) | ⟨b, -, rfl⟩) | ⟨b, -, rfl⟩) | rfl)
    · refine seqTn_valid fun q hq hf => ?_
      simp only [List.mem_cons, symL, List.mem_map] at hq
      rcases hq with rfl | ⟨a, -, rfl⟩
      · exact (declared_iff M s₁ s₂).2 (Or.inl ⟨n, hn, rfl⟩)
      · simp at hf
    · exact seqTn_valid fun q hq _ => by
        simp at hq; subst hq; exact (declared_iff M s₁ s₂).2 (Or.inr rfl)
    · exact seqTn_valid fun q hq _ => by
        simp at hq; subst hq; exact (declared_iff M s₁ s₂).2 (Or.inr rfl)
    · refine seqTn_valid fun q hq hf => ?_
      simp only [List.mem_append, symL, List.mem_map, List.mem_singleton] at hq
      rcases hq with ⟨a, -, rfl⟩ | rfl <;> simp at hf
    · exact setTn_valid fun q hq hf => by simp at hq; rcases hq with rfl | rfl <;> simp at hf

/-! ## The actions -/

theorem δ_aT {n : ℕ} (hn : n < M.trans.length) :
    (desc M s₁ s₂).toProblem.δ (aT n) = (actT M n).toAction :=
  FProbDesc.δ_of_mem (valid M s₁ s₂) ((mem_acts M).2 (Or.inl ⟨n, hn, rfl⟩))

theorem δ_aD : (desc M s₁ s₂).toProblem.δ aD = (actD).toAction :=
  FProbDesc.δ_of_mem (valid M s₁ s₂) ((mem_acts M).2 (Or.inr rfl))

theorem app_aT {n : ℕ} {s : Set ℕ} :
    (actT M n).toAction.Applicable s ↔ fq (tr M n).src ∈ s ∧ fStop ∉ s := by
  simp [actT, FActDesc.toAction, Action.Applicable, Set.disjoint_left]

theorem outcomes_aT {n : ℕ} {s : Set ℕ} :
    (actT M n).toAction.outcomes s =
      {(s \ {fq (tr M n).src}) ∪ {fq (tr M n).tgt}, s ∪ {fStop}} := by
  ext s'
  simp only [Action.outcomes, actT, FActDesc.toAction, FActDesc.effs, List.mem_cons,
    List.not_mem_nil, or_false, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨e, ⟨x, hx, rfl⟩, rfl⟩
    rcases hx with rfl | rfl
    · left; ext f; simp [Action.applyEff]
    · right; ext f; simp [Action.applyEff]
  · rintro (rfl | rfl)
    · refine ⟨_, ⟨_, Or.inl rfl, rfl⟩, ?_⟩; ext f; simp [Action.applyEff]
    · refine ⟨_, ⟨_, Or.inr rfl, rfl⟩, ?_⟩; ext f; simp [Action.applyEff]

theorem app_aD {s : Set ℕ} : (actD).toAction.Applicable s ↔ fStop ∈ s := by
  simp [actD, FActDesc.toAction, Action.Applicable]

theorem outcomes_aD {s : Set ℕ} : (actD).toAction.outcomes s = {s} := by
  ext s'
  simp [Action.outcomes, actD, FActDesc.toAction, FActDesc.effs, Action.applyEff, eq_comm]

end FU

end FOND
