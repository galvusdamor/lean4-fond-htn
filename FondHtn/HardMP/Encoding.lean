import FondHtn.Lang.Desc
/-!
# Configurations and programs of the hardness constructions

The FOND problems built in `FondHtn/HardMP/` only ever visit states of a special shape: a set of
Boolean *fields* (natural numbers, stored as the even facts `2 f`) together with exactly one
*current task* fact (odd facts, `FOND.HardMP.curF`).  Such a state is the encoding
`FOND.HardMP.Cfg.enc` of a *configuration* `FOND.HardMP.Cfg`.

Actions are given as *specifications* `FOND.HardMP.ASpec` — fields required true / false,
alternative effects on fields, and an optional requirement on (and change of) the current task —
and translated into action descriptions by `FOND.HardMP.toFAct`.  On encoded states their
semantics is computed at the level of configurations (`FOND.HardMP.applicable_enc`,
`FOND.HardMP.outcomes_enc`).

An *instruction* is a list of alternative specifications (the policy picks one, nature picks its
outcome); a *program* is a list of instructions.  Their weakest preconditions
`FOND.HardMP.wpI`, `FOND.HardMP.wpP` are sets of configurations; the block lemmas compute them
for the instruction patterns used by the constructions (guessing fields, comparing fields,
conditional copies, …).
-/

namespace FOND

namespace HardMP

/-! ## Facts -/

/-- The fact of a field. -/
def fact (f : ℕ) : ℕ := 2 * f

/-- The fact "the current task is `x`" (`none` is the root task). -/
def curF : Option (Bool × ℕ) → ℕ
  | none => 1
  | some (b, x) => 2 * (2 * x + b.toNat) + 3

theorem curF_inj {x y : Option (Bool × ℕ)} (h : curF x = curF y) : x = y := by
  rcases x with _ | ⟨b, x⟩ <;> rcases y with _ | ⟨b', y⟩ <;> simp only [curF] at h
  · rfl
  · omega
  · omega
  · cases b <;> cases b' <;> simp only [Bool.toNat_true, Bool.toNat_false] at h <;>
      first | (obtain rfl : x = y := by omega); rfl | omega

theorem fact_ne_curF (f : ℕ) (x : Option (Bool × ℕ)) : fact f ≠ curF x := by
  rcases x with _ | ⟨b, x⟩ <;> simp only [fact, curF] <;> omega

theorem fact_inj {f g : ℕ} (h : fact f = fact g) : f = g := by unfold fact at h; omega

@[simp] theorem fact_eq_fact {f g : ℕ} : fact f = fact g ↔ f = g := ⟨fact_inj, fun h => h ▸ rfl⟩

/-! ## Configurations -/

/-- A configuration: the values of the fields and the current task. -/
structure Cfg where
  /-- The values of the fields. -/
  val : ℕ → Bool
  /-- The current task (`none` = root). -/
  cur : Option (Bool × ℕ)

namespace Cfg

/-- The encoded state. -/
def enc (c : Cfg) : Set ℕ := {y | ∃ f, c.val f = true ∧ y = fact f} ∪ {curF c.cur}

@[simp] theorem fact_mem_enc {c : Cfg} {f : ℕ} : fact f ∈ c.enc ↔ c.val f = true := by
  simp only [enc, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨g, hg, h⟩ | h)
    · rwa [fact_inj h]
    · exact absurd h (fact_ne_curF _ _)
  · exact fun h => Or.inl ⟨f, h, rfl⟩

@[simp] theorem curF_mem_enc {c : Cfg} {x : Option (Bool × ℕ)} : curF x ∈ c.enc ↔ c.cur = x := by
  simp only [enc, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro (⟨g, -, h⟩ | h)
    · exact absurd h.symm (fact_ne_curF _ _)
    · exact (curF_inj h).symm
  · exact fun h => Or.inr (h ▸ rfl)

theorem enc_inj {c d : Cfg} (h : c.enc = d.enc) : c = d := by
  have hv : c.val = d.val := by
    funext f
    have := congrArg (fact f ∈ ·) h
    simp only [fact_mem_enc, eq_iff_iff] at this
    cases hc : c.val f <;> cases hd : d.val f <;> simp_all
  have hc : c.cur = d.cur := by
    have := congrArg (curF c.cur ∈ ·) h
    simp only [curF_mem_enc, eq_iff_iff, true_iff] at this
    exact this.symm
  cases c; cases d; simp_all

/-- Set a field. -/
def set (c : Cfg) (f : ℕ) (b : Bool) : Cfg := ⟨Function.update c.val f b, c.cur⟩

@[simp] theorem set_cur (c : Cfg) (f : ℕ) (b : Bool) : (c.set f b).cur = c.cur := rfl

theorem set_val (c : Cfg) (f : ℕ) (b : Bool) (g : ℕ) :
    (c.set f b).val g = if g = f then b else c.val g := by
  simp only [set, Function.update_apply]

@[simp] theorem set_val_self (c : Cfg) (f : ℕ) (b : Bool) : (c.set f b).val f = b := by
  simp [set_val]

theorem set_val_ne (c : Cfg) {f g : ℕ} (b : Bool) (h : g ≠ f) : (c.set f b).val g = c.val g := by
  simp [set_val, h]

/-- Set the fields `fs` to the values of `g`, one after the other. -/
def sets (c : Cfg) (fs : List ℕ) (g : ℕ → Bool) : Cfg := fs.foldl (fun c f => c.set f (g f)) c

@[simp] theorem sets_nil (c : Cfg) (g : ℕ → Bool) : c.sets [] g = c := rfl

theorem sets_cons (c : Cfg) (f : ℕ) (fs : List ℕ) (g : ℕ → Bool) :
    c.sets (f :: fs) g = (c.set f (g f)).sets fs g := rfl

@[simp] theorem sets_cur (c : Cfg) (fs : List ℕ) (g : ℕ → Bool) : (c.sets fs g).cur = c.cur := by
  induction fs generalizing c with
  | nil => rfl
  | cons f fs ih => rw [sets_cons, ih]; rfl

theorem sets_val (c : Cfg) (fs : List ℕ) (g : ℕ → Bool) (x : ℕ) :
    (c.sets fs g).val x = if x ∈ fs then g x else c.val x := by
  induction fs generalizing c with
  | nil => simp
  | cons f fs ih =>
    rw [sets_cons, ih]
    by_cases hx : x ∈ fs
    · simp [hx]
    · by_cases hxf : x = f
      · subst hxf; simp [hx]
      · simp [hx, hxf, set_val_ne _ _ hxf]

/-- Copy fields `(f, g)` (`g := f`), one after the other. -/
def cps (c : Cfg) (ps : List (ℕ × ℕ)) : Cfg := ps.foldl (fun c q => c.set q.2 (c.val q.1)) c

@[simp] theorem cps_nil (c : Cfg) : c.cps [] = c := rfl

theorem cps_cons (c : Cfg) (q : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    c.cps (q :: ps) = (c.set q.2 (c.val q.1)).cps ps := rfl

@[simp] theorem cps_cur (c : Cfg) (ps : List (ℕ × ℕ)) : (c.cps ps).cur = c.cur := by
  induction ps generalizing c with
  | nil => rfl
  | cons q ps ih => rw [cps_cons, ih]; rfl

theorem cps_val_not (c : Cfg) (ps : List (ℕ × ℕ)) {x : ℕ} (hx : x ∉ ps.map Prod.snd) :
    (c.cps ps).val x = c.val x := by
  induction ps generalizing c with
  | nil => rfl
  | cons q ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    rw [cps_cons, ih _ hx.2, set_val_ne _ _ hx.1]

theorem cps_val_mem (c : Cfg) (ps : List (ℕ × ℕ)) (hsrc : ∀ q ∈ ps, q.1 ∉ ps.map Prod.snd)
    (hnd : (ps.map Prod.snd).Nodup) {q : ℕ × ℕ} (hq : q ∈ ps) : (c.cps ps).val q.2 = c.val q.1 := by
  induction ps generalizing c with
  | nil => simp at hq
  | cons r ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [cps_cons]
    rcases List.mem_cons.1 hq with rfl | hq
    · rw [cps_val_not _ _ hnd.1, set_val_self]
    · have hr : q.2 ≠ r.2 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hq)
      have h1 : q.1 ≠ r.2 := fun h => hsrc q (by simp [hq]) (by simp [h])
      rw [ih _ (fun a ha => fun h => hsrc a (by simp [ha]) (by simp [h])) hnd.2 hq,
        set_val_ne _ _ h1]

end Cfg

theorem fact_or_curF (y : ℕ) : (∃ f, y = fact f) ∨ ∃ x, y = curF x := by
  rcases Nat.even_or_odd y with ⟨f, hf⟩ | ⟨m, hm⟩
  · exact Or.inl ⟨f, by unfold fact; omega⟩
  · right
    rcases m with _ | m
    · exact ⟨none, by simp [curF]; omega⟩
    · rcases Nat.even_or_odd m with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact ⟨some (false, x), by simp [curF]; omega⟩
      · exact ⟨some (true, x), by simp [curF]; omega⟩

/-! ## Action specifications -/

/-- An action specification: fields required true, fields required false, alternative effects
on the fields, required current task(s), new current task (at most one). -/
abbrev ASpec : Type :=
  List ℕ × List ℕ × List (List ℕ × List ℕ) × List (Option (Bool × ℕ)) × List (Option (Bool × ℕ))

namespace ASpec

/-- Fields required true. -/
def pre (a : ASpec) : List ℕ := a.1
/-- Fields required false. -/
def neg (a : ASpec) : List ℕ := a.2.1
/-- Alternative effects. -/
def effs (a : ASpec) : List (List ℕ × List ℕ) := a.2.2.1
/-- Required current task. -/
def cpre (a : ASpec) : List (Option (Bool × ℕ)) := a.2.2.2.1
/-- New current task. -/
def cnew (a : ASpec) : List (Option (Bool × ℕ)) := a.2.2.2.2

/-- Well-formed specifications: at most one new current task, which requires an old one. -/
def WF (a : ASpec) : Prop := a.cnew.length ≤ 1 ∧ (a.cnew ≠ [] → a.cpre ≠ [])

/-- Applicability on configurations. -/
def App (a : ASpec) (c : Cfg) : Prop :=
  (∀ f ∈ a.pre, c.val f = true) ∧ (∀ f ∈ a.neg, c.val f = false) ∧ ∀ x ∈ a.cpre, c.cur = x

/-- The configuration after the effect `e`. -/
def eff (a : ASpec) (e : List ℕ × List ℕ) (c : Cfg) : Cfg :=
  ⟨fun f => (c.val f && !decide (f ∈ e.2)) || decide (f ∈ e.1), a.cnew.headD c.cur⟩

/-- The outcomes on configurations. -/
def Out (a : ASpec) (c : Cfg) : Set Cfg := {c' | ∃ e ∈ a.effs, c' = a.eff e c}

end ASpec

/-- **The action description of a specification.** -/
def toFAct (nm : ℕ) (a : ASpec) : FActDesc :=
  (nm, a.1.map fact ++ a.2.2.2.1.map curF, a.2.1.map fact,
    a.2.2.1.map fun e => (e.1.map fact ++ a.2.2.2.2.map curF,
      e.2.map fact ++ (bif a.2.2.2.2.isEmpty then [] else a.2.2.2.1.map curF)))

theorem applicable_enc (nm : ℕ) (a : ASpec) (c : Cfg) :
    (toFAct nm a).toAction.Applicable c.enc ↔ a.App c := by
  simp only [Action.Applicable, FActDesc.toAction, toFAct, ASpec.App, ASpec.pre, ASpec.neg,
    ASpec.cpre]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => ?_, fun f hf => ?_, fun x hx => ?_⟩
    · exact Cfg.fact_mem_enc.1 (h1 (by
        simp only [Set.mem_setOf_eq, List.mem_append, List.mem_map]; exact Or.inl ⟨f, hf, rfl⟩))
    · have hm : fact f ∈ {y | y ∈ a.2.1.map fact} := by
        simp only [Set.mem_setOf_eq, List.mem_map]; exact ⟨f, hf, rfl⟩
      have := Set.disjoint_left.mp h2 hm
      rw [Cfg.fact_mem_enc] at this
      simpa using this
    · exact Cfg.curF_mem_enc.1 (h1 (by
        simp only [Set.mem_setOf_eq, List.mem_append, List.mem_map]; exact Or.inr ⟨x, hx, rfl⟩))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun y hy => ?_, Set.disjoint_left.2 fun y hy hy' => ?_⟩
    · simp only [Set.mem_setOf_eq, List.mem_append, List.mem_map] at hy
      rcases hy with ⟨f, hf, rfl⟩ | ⟨x, hx, rfl⟩
      · exact Cfg.fact_mem_enc.2 (h1 f hf)
      · exact Cfg.curF_mem_enc.2 (h3 x hx)
    · simp only [Set.mem_setOf_eq, List.mem_map] at hy
      obtain ⟨f, hf, rfl⟩ := hy
      rw [Cfg.fact_mem_enc, h2 f hf] at hy'
      exact Bool.false_ne_true hy'

theorem applyEff_enc {a : ASpec} (hwf : a.WF) {c : Cfg} (happ : a.App c)
    (e : List ℕ × List ℕ) :
    Action.applyEff ({f | f ∈ e.1.map fact ++ a.cnew.map curF},
      {f | f ∈ e.2.map fact ++ (bif a.cnew.isEmpty then [] else a.cpre.map curF)}) c.enc =
      (a.eff e c).enc := by
  ext y
  simp only [Action.applyEff, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, List.mem_append,
    List.mem_map]
  rcases fact_or_curF y with ⟨f, rfl⟩ | ⟨x, rfl⟩
  · simp only [Cfg.fact_mem_enc, ASpec.eff, fact_eq_fact,
      Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq]
    have h1 : ¬ ∃ x ∈ a.cnew, curF x = fact f := fun ⟨x, _, h⟩ => fact_ne_curF _ _ h.symm
    have h2 : fact f ∉ {f | f ∈ (bif a.cnew.isEmpty then [] else a.cpre.map curF)} := by
      cases a.cnew.isEmpty <;> simp [fun x => (fact_ne_curF f x).symm]
    simp only [Set.mem_setOf_eq] at h2
    simp [h1, h2]
  · simp only [Cfg.curF_mem_enc, ASpec.eff]
    have hn : ¬ ∃ g ∈ e.1, fact g = curF x := fun ⟨g, _, h⟩ => fact_ne_curF _ _ h
    have hn' : ¬ ∃ g ∈ e.2, fact g = curF x := fun ⟨g, _, h⟩ => fact_ne_curF _ _ h
    obtain ⟨hlen, hcp⟩ := hwf
    rcases hc : a.cnew with _ | ⟨z, _ | ⟨z', l⟩⟩
    · simp [hn, hn']
    · have hne : a.cpre ≠ [] := hcp (by rw [hc]; simp)
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
      have hcw : c.cur = w := happ.2.2 w hw
      have hcp' : ∀ v ∈ a.cpre, v = c.cur := fun v hv => (happ.2.2 v hv).symm
      simp only [hn, hn', List.isEmpty_cons, cond_false, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false, exists_eq_left, false_or, List.headD_cons]
      constructor
      · rintro (⟨h, h'⟩ | h)
        · exact absurd ⟨c.cur, hcw ▸ hw, by rw [h]⟩ h'
        · exact curF_inj h
      · intro h; exact Or.inr (by rw [h])
    · rw [hc] at hlen; simp at hlen

theorem outcomes_enc (nm : ℕ) {a : ASpec} (hwf : a.WF) {c : Cfg} (happ : a.App c) :
    (toFAct nm a).toAction.outcomes c.enc = Cfg.enc '' a.Out c := by
  ext s'
  simp only [Action.outcomes, FActDesc.toAction, FActDesc.effs, toFAct, List.mem_map,
    Set.mem_setOf_eq, Set.mem_image, ASpec.Out]
  constructor
  · rintro ⟨e', ⟨x, ⟨e, he, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, (applyEff_enc hwf happ e).symm⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨e, he, rfl⟩, rfl⟩, (applyEff_enc hwf happ e).symm⟩

/-! ## Instructions and programs -/

/-- Weakest precondition of an instruction (a list of alternatives). -/
def wpI (ins : List ASpec) (Ψ : Set Cfg) : Set Cfg :=
  {c | ∃ a ∈ ins, a.App c ∧ ∀ c' ∈ a.Out c, c' ∈ Ψ}

/-- Weakest precondition of a program. -/
def wpP (prog : List (List ASpec)) (Ψ : Set Cfg) : Set Cfg := prog.foldr wpI Ψ

@[simp] theorem wpP_nil (Ψ : Set Cfg) : wpP [] Ψ = Ψ := rfl

theorem wpP_cons (ins : List ASpec) (prog : List (List ASpec)) (Ψ : Set Cfg) :
    wpP (ins :: prog) Ψ = wpI ins (wpP prog Ψ) := rfl

theorem wpP_append (p₁ p₂ : List (List ASpec)) (Ψ : Set Cfg) :
    wpP (p₁ ++ p₂) Ψ = wpP p₁ (wpP p₂ Ψ) := List.foldr_append

theorem wpI_mono {ins : List ASpec} {Ψ Ψ' : Set Cfg} (h : Ψ ⊆ Ψ') : wpI ins Ψ ⊆ wpI ins Ψ' :=
  fun _ ⟨a, ha, happ, hall⟩ => ⟨a, ha, happ, fun c' hc' => h (hall c' hc')⟩

theorem wpP_mono (prog : List (List ASpec)) {Ψ Ψ' : Set Cfg} (h : Ψ ⊆ Ψ') :
    wpP prog Ψ ⊆ wpP prog Ψ' := by
  induction prog with
  | nil => exact h
  | cons ins prog ih => exact wpI_mono ih

/-! ## Instruction patterns -/

/-- The single empty effect. -/
def noeff : List (List ℕ × List ℕ) := [([], [])]

/-- Guess the field `f`. -/
def guessI (f : ℕ) : List ASpec :=
  [([], [], [([f], [])], [], []), ([], [], [([], [f])], [], [])]

/-- Check `f = g`. -/
def eqI (f g : ℕ) : List ASpec := [([f, g], [], noeff, [], []), ([], [f, g], noeff, [], [])]

/-- If `s` holds, copy `f` to `g`. -/
def ccpI (s f g : ℕ) : List ASpec :=
  [([], [s], noeff, [], []), ([s, f], [], [([g], [])], [], []), ([s], [f], [([], [g])], [], [])]

/-- If `s` holds, the current task must be `h` and becomes `y`. -/
def ccurI (s : ℕ) (h y : Option (Bool × ℕ)) : List ASpec :=
  [([], [s], noeff, [], []), ([s], [], noeff, [h], [y])]

/-- A deterministic check without effect. -/
def chkI (pre neg : List ℕ) (cpre : List (Option (Bool × ℕ))) : List ASpec :=
  [(pre, neg, noeff, cpre, [])]

/-- Set the field `d`. -/
def setI (d : ℕ) : List ASpec := [([], [], [([d], [])], [], [])]

/-- Nature picks `i < k`: the field `sel i` is set, the other `sel i'` (`i' < k`) are cleared. -/
def pickI (sel : ℕ → ℕ) (k : ℕ) : List ASpec :=
  [([], [], (List.range k).map fun i => ([sel i], (List.range k).map sel), [], [])]

@[simp] theorem eff_nil' (pre neg : List ℕ) (effs : List (List ℕ × List ℕ))
    (cpre : List (Option (Bool × ℕ))) (c : Cfg) :
    ASpec.eff (pre, neg, effs, cpre, []) ([], []) c = c := by
  cases c; simp [ASpec.eff, ASpec.cnew]

@[simp] theorem eff_add' (pre neg : List ℕ) (effs : List (List ℕ × List ℕ))
    (cpre : List (Option (Bool × ℕ))) (c : Cfg) (g : ℕ) :
    ASpec.eff (pre, neg, effs, cpre, []) ([g], []) c = c.set g true := by
  simp only [ASpec.eff, ASpec.cnew, List.headD_nil, Cfg.set]
  congr 1; funext f
  by_cases hf : f = g <;> simp [hf, Function.update_apply]

@[simp] theorem eff_del' (pre neg : List ℕ) (effs : List (List ℕ × List ℕ))
    (cpre : List (Option (Bool × ℕ))) (c : Cfg) (g : ℕ) :
    ASpec.eff (pre, neg, effs, cpre, []) ([], [g]) c = c.set g false := by
  simp only [ASpec.eff, ASpec.cnew, List.headD_nil, Cfg.set]
  congr 1; funext f
  by_cases hf : f = g <;> simp [hf, Function.update_apply]

@[simp] theorem app_iff (pre neg : List ℕ) (effs : List (List ℕ × List ℕ))
    (cpre cnew : List (Option (Bool × ℕ))) (c : Cfg) :
    ASpec.App (pre, neg, effs, cpre, cnew) c ↔
      (∀ f ∈ pre, c.val f = true) ∧ (∀ f ∈ neg, c.val f = false) ∧ ∀ x ∈ cpre, c.cur = x :=
  Iff.rfl

theorem mem_wpI_iff {ins : List ASpec} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI ins Ψ ↔ ∃ a ∈ ins, a.App c ∧ ∀ e ∈ a.effs, a.eff e c ∈ Ψ := by
  simp only [wpI, ASpec.Out, Set.mem_setOf_eq]
  refine exists_congr fun a => and_congr Iff.rfl (and_congr Iff.rfl ?_)
  exact ⟨fun h e he => h _ ⟨e, he, rfl⟩, fun h c' ⟨e, he, hc'⟩ => hc' ▸ h e he⟩

theorem mem_wpI_guess {f : ℕ} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI (guessI f) Ψ ↔ ∃ b, c.set f b ∈ Ψ := by
  rw [mem_wpI_iff]
  simp only [guessI, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, app_iff, ASpec.effs, forall_eq, eff_add', eff_del']
  simp only [IsEmpty.forall_iff, implies_true, and_self, true_and]
  constructor
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inr hb
    · exact Or.inl hb

theorem Cfg.sets_congr (c : Cfg) {fs : List ℕ} {g g' : ℕ → Bool} (h : ∀ x ∈ fs, g x = g' x) :
    c.sets fs g = c.sets fs g' := by
  induction fs generalizing c with
  | nil => rfl
  | cons f fs ih =>
    rw [Cfg.sets_cons, Cfg.sets_cons, h f (by simp), ih _ fun x hx => h x (by simp [hx])]

/-- **Guessing a list of fields.** -/
theorem mem_wpP_guess {fs : List ℕ} (hnd : fs.Nodup) {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpP (fs.map guessI) Ψ ↔ ∃ g : ℕ → Bool, c.sets fs g ∈ Ψ := by
  induction fs generalizing c with
  | nil => exact ⟨fun h => ⟨fun _ => true, h⟩, fun ⟨_, h⟩ => h⟩
  | cons f fs ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, wpP_cons, mem_wpI_guess]
    simp only [ih hnd.2]
    constructor
    · rintro ⟨b, g, hg⟩
      refine ⟨Function.update g f b, ?_⟩
      rw [Cfg.sets_cons, Function.update_self,
        Cfg.sets_congr _ (g := Function.update g f b) (g' := g) fun x hx =>
          Function.update_of_ne (fun h => hnd.1 (by rw [← h]; exact hx)) _ _]
      exact hg
    · rintro ⟨g, hg⟩
      exact ⟨g f, g, hg⟩

theorem mem_wpI_eq {f g : ℕ} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI (eqI f g) Ψ ↔ c.val f = c.val g ∧ c ∈ Ψ := by
  rw [mem_wpI_iff]
  simp only [eqI, noeff, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, app_iff, ASpec.effs, forall_eq, eff_nil', forall_eq_or_imp,
    IsEmpty.forall_iff, implies_true, and_true]
  cases hf : c.val f <;> cases hg : c.val g <;> simp

/-- **Comparing pairs of fields.** -/
theorem mem_wpP_eq {ps : List (ℕ × ℕ)} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpP (ps.map fun q => eqI q.1 q.2) Ψ ↔ (∀ q ∈ ps, c.val q.1 = c.val q.2) ∧ c ∈ Ψ := by
  induction ps with
  | nil => simp
  | cons q ps ih =>
    rw [List.map_cons, wpP_cons, mem_wpI_eq, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem mem_wpI_ccp {s f g : ℕ} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI (ccpI s f g) Ψ ↔ if c.val s = true then c.set g (c.val f) ∈ Ψ else c ∈ Ψ := by
  rw [mem_wpI_iff]
  simp only [ccpI, noeff, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, app_iff, ASpec.effs, forall_eq, eff_nil', eff_add', eff_del',
    forall_eq_or_imp, IsEmpty.forall_iff, implies_true, and_true]
  cases hs : c.val s <;> cases hf : c.val f <;> simp

/-- Conditional copies whose condition fails do nothing. -/
theorem mem_wpP_ccp_off {s : ℕ} {ps : List (ℕ × ℕ)} {Ψ : Set Cfg} {c : Cfg}
    (hs : c.val s = false) : c ∈ wpP (ps.map fun q => ccpI s q.1 q.2) Ψ ↔ c ∈ Ψ := by
  induction ps with
  | nil => rfl
  | cons q ps ih => rw [List.map_cons, wpP_cons, mem_wpI_ccp, if_neg (by simp [hs]), ih]

/-- Conditional copies whose condition holds copy. -/
theorem mem_wpP_ccp_on {s : ℕ} {ps : List (ℕ × ℕ)} (hps : s ∉ ps.map Prod.snd) {Ψ : Set Cfg}
    {c : Cfg} (hs : c.val s = true) :
    c ∈ wpP (ps.map fun q => ccpI s q.1 q.2) Ψ ↔ c.cps ps ∈ Ψ := by
  induction ps generalizing c with
  | nil => rfl
  | cons q ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hps
    rw [List.map_cons, wpP_cons, mem_wpI_ccp, if_pos hs, ih hps.2 (by
      rw [Cfg.set_val_ne _ _ hps.1]; exact hs), Cfg.cps_cons]

theorem mem_wpI_ccur {s : ℕ} {h y : Option (Bool × ℕ)} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI (ccurI s h y) Ψ ↔
      if c.val s = true then c.cur = h ∧ (⟨c.val, y⟩ : Cfg) ∈ Ψ else c ∈ Ψ := by
  rw [mem_wpI_iff]
  have he : ASpec.eff ([s], [], noeff, [h], [y]) ([], []) c = ⟨c.val, y⟩ := by
    simp [ASpec.eff, ASpec.cnew]
  simp only [ccurI, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, app_iff, ASpec.effs, noeff, forall_eq, eff_nil', IsEmpty.forall_iff,
    implies_true, and_true, true_and]
  rw [show ([([], [])] : List (List ℕ × List ℕ)) = noeff from rfl, he]
  cases hs : c.val s <;> simp

theorem mem_wpI_chk {pre neg : List ℕ} {cpre : List (Option (Bool × ℕ))} {Ψ : Set Cfg}
    {c : Cfg} : c ∈ wpI (chkI pre neg cpre) Ψ ↔
      ((∀ f ∈ pre, c.val f = true) ∧ (∀ f ∈ neg, c.val f = false) ∧ ∀ x ∈ cpre, c.cur = x) ∧
        c ∈ Ψ := by
  rw [mem_wpI_iff]
  simp [chkI, noeff, ASpec.effs]

theorem mem_wpI_set {d : ℕ} {Ψ : Set Cfg} {c : Cfg} : c ∈ wpI (setI d) Ψ ↔ c.set d true ∈ Ψ := by
  rw [mem_wpI_iff]
  simp [setI, ASpec.effs]

/-- The configuration after nature picked `i`. -/
def Cfg.pick (c : Cfg) (sel : ℕ → ℕ) (k i : ℕ) : Cfg :=
  ⟨fun f => (c.val f && !decide (f ∈ (List.range k).map sel)) || decide (f ∈ [sel i]), c.cur⟩

theorem mem_wpI_pick {sel : ℕ → ℕ} {k : ℕ} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI (pickI sel k) Ψ ↔ ∀ i < k, c.pick sel k i ∈ Ψ := by
  rw [mem_wpI_iff]
  simp only [pickI, List.mem_singleton, exists_eq_left, app_iff, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_self, true_and, ASpec.effs, List.mem_map,
    List.mem_range, forall_exists_index, and_imp]
  constructor
  · intro h i hi
    have := h _ i hi rfl
    simpa [ASpec.eff, ASpec.cnew, Cfg.pick] using this
  · rintro h e i hi rfl
    have := h i hi
    simpa [ASpec.eff, ASpec.cnew, Cfg.pick] using this

theorem Cfg.pick_val_sel {c : Cfg} {sel : ℕ → ℕ} (hsel : Function.Injective sel) {k i i' : ℕ}
    (hi' : i' < k) : (c.pick sel k i).val (sel i') = decide (i' = i) := by
  have h1 : sel i' ∈ (List.range k).map sel := List.mem_map.2 ⟨i', List.mem_range.2 hi', rfl⟩
  simp only [Cfg.pick, h1, decide_true, Bool.not_true, Bool.and_false, Bool.false_or,
    List.mem_singleton, hsel.eq_iff]

theorem Cfg.pick_val_ne {c : Cfg} {sel : ℕ → ℕ} {k i f : ℕ} (hf : ∀ i', f ≠ sel i') :
    (c.pick sel k i).val f = c.val f := by
  simp only [Cfg.pick, List.mem_map, List.mem_range, List.mem_singleton]
  have h1 : ¬ ∃ a, a < k ∧ sel a = f := fun ⟨a, _, h⟩ => hf a h.symm
  simp [h1, hf i]

@[simp] theorem Cfg.pick_cur (c : Cfg) (sel : ℕ → ℕ) (k i : ℕ) : (c.pick sel k i).cur = c.cur :=
  rfl

/-- All instruction patterns are well formed. -/
theorem guessI_wf (f : ℕ) : ∀ a ∈ guessI f, a.WF := by
  simp [guessI, ASpec.WF, ASpec.cnew]
theorem eqI_wf (f g : ℕ) : ∀ a ∈ eqI f g, a.WF := by simp [eqI, ASpec.WF, ASpec.cnew]
theorem ccpI_wf (s f g : ℕ) : ∀ a ∈ ccpI s f g, a.WF := by simp [ccpI, ASpec.WF, ASpec.cnew]
theorem ccurI_wf (s : ℕ) (h y : Option (Bool × ℕ)) : ∀ a ∈ ccurI s h y, a.WF := by
  simp [ccurI, ASpec.WF, ASpec.cnew, ASpec.cpre]
theorem chkI_wf (pre neg : List ℕ) (cpre : List (Option (Bool × ℕ))) :
    ∀ a ∈ chkI pre neg cpre, a.WF := by simp [chkI, ASpec.WF, ASpec.cnew]
theorem setI_wf (d : ℕ) : ∀ a ∈ setI d, a.WF := by simp [setI, ASpec.WF, ASpec.cnew]
theorem pickI_wf (sel : ℕ → ℕ) (k : ℕ) : ∀ a ∈ pickI sel k, a.WF := by
  simp [pickI, ASpec.WF, ASpec.cnew]

end HardMP

end FOND
