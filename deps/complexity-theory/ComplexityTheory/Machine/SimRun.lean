import ComplexityTheory.Machine.SimDef
/-!
# A single-tape Turing machine simulating a stack machine: one instruction

The routines of `HTN.Mach.simM` as segments of runs (`TM.NTM.Seg`): moving (`seg_mvTo_right`,
`seg_mvTo_left`), walking up a stack (`seg_scanUp`), walking back home (`seg_rScan`), and the
simulation of one instruction of the stack machine from the configuration `good n σ`
(`HTN.Mach.sim_step`, completeness) together with the converse (`HTN.Mach.sim_back`,
soundness): every accepting run from `good n σ` starts with the simulation of a step of the
stack machine, unless `σ` is accepting.
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM

variable {C : List Ins} {K kin : ℕ}

/-- The configuration after the transition `t`. -/
def nxt (c : Config QS Sym) (t : Tr) : Config QS Sym :=
  ⟨t.1, t.2.2.apply c.head, Function.update c.tape c.head t.2.1⟩

theorem step_iff {c d : Config QS Sym} :
    (simM C K kin).Step c d ↔ ∃ t ∈ δ C K kin c.state (c.tape c.head), d = nxt c t := by
  constructor
  · rintro ⟨q', γ', m, ht, rfl⟩; exact ⟨(q', γ', m), ht, rfl⟩
  · rintro ⟨⟨q', γ', m⟩, ht, rfl⟩; exact ⟨q', γ', m, ht, rfl⟩

theorem notAcc_mv {right : Bool} {r : ℕ} {tgt : Phase} :
    QS.mv right r tgt ∉ (simM C K kin).accept := by
  rintro ⟨pc, h, -⟩; cases h

theorem notAcc_base {ph : Phase} (h : ∀ pc, ph ≠ .exec pc) :
    QS.base ph ∉ (simM C K kin).accept := by
  rintro ⟨pc, e, -⟩; cases e; exact h pc rfl

theorem notAcc_mvTo {right : Bool} {r : ℕ} {tgt : Phase} (h : ∀ pc, tgt ≠ .exec pc) :
    mvTo right r tgt ∉ (simM C K kin).accept := by
  cases r
  · exact notAcc_base h
  · exact notAcc_mv

theorem notAcc_exec {pc : ℕ} (h : C[pc]? ≠ some .accept) :
    QS.base (.exec pc) ∉ (simM C K kin).accept := by
  rintro ⟨pc', e, h'⟩; cases e; exact h h'

/-- **A deterministic step.** -/
theorem seg_det {Sp : ℕ} {c : Config QS Sym} {t : Tr} (hδ : δ C K kin c.state (c.tape c.head) = [t])
    (hna : c.state ∉ (simM C K kin).accept) (h₁ : c.head < Sp) (h₂ : t.2.2.apply c.head < Sp) :
    (simM C K kin).Seg Sp c (nxt c t) 1 := by
  refine NTM.Seg.single hna (fun d => ?_) h₁ h₂
  rw [step_iff, hδ]; simp

theorem nxt_same {c : Config QS Sym} {q : QS} {m : Move} :
    nxt c (q, c.tape c.head, m) = ⟨q, m.apply c.head, c.tape⟩ := by
  simp [nxt]

/-! ### Moving -/

theorem seg_mvTo_right {Sp : ℕ} (tgt : Phase) (tape : ℕ → Sym) :
    ∀ (r h : ℕ), h + r < Sp →
      (simM C K kin).Seg Sp ⟨mvTo true r tgt, h, tape⟩ ⟨.base tgt, h + r, tape⟩ r := by
  intro r
  induction r with
  | zero => intro h hS; exact NTM.Seg.refl (by simpa using hS)
  | succ r ih =>
    intro h hS
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨mvTo true (r + 1) tgt, h, tape⟩) (t := (mvTo true r tgt, tape h, .right)) rfl
      notAcc_mv (by simp; omega) (by simp [Move.apply]; omega)
    rw [nxt_same] at h1
    have h2 := ih (h + 1) (by omega)
    simp only [Move.apply] at h1
    rw [show h + (r + 1) = h + 1 + r by omega]
    exact (h1.trans h2).of_eq (by omega)

theorem seg_mvTo_left {Sp : ℕ} (tgt : Phase) (tape : ℕ → Sym) :
    ∀ (r h : ℕ), r ≤ h → h < Sp →
      (simM C K kin).Seg Sp ⟨mvTo false r tgt, h, tape⟩ ⟨.base tgt, h - r, tape⟩ r := by
  intro r
  induction r with
  | zero => intro h _ hS; exact NTM.Seg.refl (by simpa using hS)
  | succ r ih =>
    intro h hr hS
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨mvTo false (r + 1) tgt, h, tape⟩) (t := (mvTo false r tgt, tape h, .left)) rfl
      notAcc_mv (by simp; omega) (by simp [Move.apply]; omega)
    rw [nxt_same] at h1
    have h2 := ih (h - 1) (by omega) (by omega)
    simp only [Move.apply] at h1
    rw [show h - (r + 1) = h - 1 - r by omega]
    exact (h1.trans h2).of_eq (by omega)


theorem nxt_same' {c : Config QS Sym} {q : QS} {m : Move} {γ : Sym} (h : c.tape c.head = γ) :
    nxt c (q, γ, m) = ⟨q, m.apply c.head, c.tape⟩ := by
  subst h; exact nxt_same

theorem cell_succ (n j r : ℕ) : cell K n (j + 1) r = cell K n j r + (K + 1) := by
  unfold cell; ring

theorem cell_add {n j r : ℕ} (d : ℕ) : cell K n j r + d = cell K n j (r + d) := by
  unfold cell; ring

/-! ### Walking up a stack and back home -/

/-- **Walking up the track of stack `k`** to its first blank cell. -/
theorem seg_scanUp {Sp n : ℕ} (S : Store) {k : ℕ} (hk : k < K) (act : Act) (cont : Option ℕ)
    (hSp : cell K n (S k).length k < Sp) :
    ∀ d j, j + d = (S k).length →
      (simM C K kin).Seg Sp ⟨.base (.scan act k cont (decide (j = 0))), cell K n j k, lay K n S⟩
        ⟨.base (.scan act k cont (decide ((S k).length = 0))), cell K n (S k).length k, lay K n S⟩
        (d * (K + 1)) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    simp only [Nat.add_zero] at hj; subst hj
    exact (NTM.Seg.refl (N := simM C K kin) (c := ⟨QS.base (.scan act k cont (decide ((S k).length = 0))),
      cell K n (S k).length k, lay K n S⟩) hSp).of_eq (by ring)
  | succ d ih =>
    intro j hj
    have hjl : j < (S k).length := by omega
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, lay K n S (cell K n j k) = some c₀ := by
      rw [lay_track _ hk]
      exact ⟨_, List.getElem?_eq_getElem (by simpa using hjl)⟩
    have hle : cell K n (j + 1) k ≤ cell K n (S k).length k := by unfold cell; nlinarith
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.scan act k cont (decide (j = 0))), cell K n j k, lay K n S⟩)
      (t := (mvTo true K (.scan act k cont false), some c₀, .right))
      (by simp only; rw [hc₀]; rfl) (notAcc_base (by intro pc h; cases h))
      (show cell K n j k < Sp by rw [cell_succ] at hle; omega)
      (show cell K n j k + 1 < Sp by rw [cell_succ] at hle; omega)
    rw [nxt_same' hc₀] at h1
    have h2 := seg_mvTo_right (C := C) (K := K) (kin := kin) (Sp := Sp)
      (.scan act k cont false) (lay K n S) K (cell K n j k + 1) (by rw [cell_succ] at hle; omega)
    have h3 := ih (j + 1) (by omega)
    simp only [show decide (j + 1 = 0) = false by simp] at h3
    rw [show cell K n j k + 1 + K = cell K n (j + 1) k by rw [cell_succ]; ring] at h2
    exact ((h1.trans h2).trans h3).of_eq (by ring)

/-- **Walking back home** from the marker cell of block `j`. -/
theorem seg_rScan {Sp n : ℕ} (S : Store) (cont : Option ℕ) :
    ∀ j, cell K n j K < Sp →
      (simM C K kin).Seg Sp ⟨.base (.rScan cont), cell K n j K, lay K n S⟩
        ⟨.base (contPh cont), home K n, lay K n S⟩ (j * (K + 1) + 1) := by
  intro j
  induction j with
  | zero =>
    intro hSp
    have hm : lay K n S (cell K n 0 K) = some true := by rw [lay_marker]; rfl
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.rScan cont), cell K n 0 K, lay K n S⟩)
      (t := (.base (contPh cont), some true, .stay))
      (by simp only; rw [hm]; rfl) (notAcc_base (by intro pc h; cases h)) hSp
      (by simpa [Move.apply] using hSp)
    rw [nxt_same' hm] at h1
    simpa [Move.apply, home_eq] using h1
  | succ j ih =>
    intro hSp
    have hm : lay K n S (cell K n (j + 1) K) = none := by rw [lay_marker]; simp
    have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.rScan cont), cell K n (j + 1) K, lay K n S⟩)
      (t := (mvTo false K (.rScan cont), none, .left))
      (by simp only; rw [hm]; rfl) (notAcc_base (by intro pc h; cases h)) hSp
      (by simp only [Move.apply]; omega)
    rw [nxt_same' hm] at h1
    simp only [Move.apply] at h1
    have h2 := seg_mvTo_left (C := C) (K := K) (kin := kin) (Sp := Sp) (.rScan cont) (lay K n S) K
      (cell K n (j + 1) K - 1) (by rw [cell_succ]; omega) (by omega)
    rw [show cell K n (j + 1) K - 1 - K = cell K n j K by rw [cell_succ]; omega] at h2
    have h3 := ih (by rw [cell_succ] at hSp; omega)
    exact ((h1.trans h2).trans h3).of_eq (by ring)

/-- **Finishing a routine**: from the track of stack `k` in block `j`, to the marker of the
block and back home. -/
theorem seg_finish {Sp n : ℕ} (S : Store) {k : ℕ} (hk : k < K) (cont : Option ℕ) (j : ℕ)
    (hSp : cell K n j K < Sp) :
    (simM C K kin).Seg Sp ⟨mvTo true (K - k) (.rScan cont), cell K n j k, lay K n S⟩
      ⟨.base (contPh cont), home K n, lay K n S⟩ ((K - k) + (j * (K + 1) + 1)) := by
  have h1 := seg_mvTo_right (C := C) (K := K) (kin := kin) (Sp := Sp) (.rScan cont) (lay K n S)
    (K - k) (cell K n j k) (by rw [cell_add]; rwa [show k + (K - k) = K by omega])
  rw [cell_add, show k + (K - k) = K by omega] at h1
  exact h1.trans (seg_rScan S cont j hSp)

/-- **Starting a routine** from home: to the track of stack `k` in block `0`, then up the
stack. -/
theorem seg_start {Sp n pc : ℕ} (S : Store) {k : ℕ} (hk : k < K) (act : Act) (cont : Option ℕ)
    (hex : ∀ γ, execTr C K pc γ = startTr K act k cont γ) (hna : C[pc]? ≠ some .accept)
    (hSp : cell K n (S k).length K < Sp) :
    (simM C K kin).Seg Sp (good K n ⟨pc, S⟩)
      ⟨.base (.scan act k cont (decide ((S k).length = 0))), cell K n (S k).length k, lay K n S⟩
      (1 + (K - k - 1) + (S k).length * (K + 1)) := by
  have hle : cell K n 0 K ≤ cell K n (S k).length K := by unfold cell; nlinarith
  have hh : home K n = cell K n 0 K := home_eq n
  have h1 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp) (c := good K n ⟨pc, S⟩)
    (t := (mvTo false (K - k - 1) (.scan act k cont true), lay K n S (home K n), .left))
    (by simp only [good, δ, phaseTr]; rw [hex]; rfl) (notAcc_exec hna)
    (show home K n < Sp by omega) (show home K n - 1 < Sp by omega)
  rw [show good K n ⟨pc, S⟩ = ⟨.base (.exec pc), home K n, lay K n S⟩ from rfl, nxt_same] at h1
  simp only [Move.apply] at h1
  have h2 := seg_mvTo_left (C := C) (K := K) (kin := kin) (Sp := Sp) (.scan act k cont true)
    (lay K n S) (K - k - 1) (home K n - 1) (by rw [hh]; unfold cell; omega) (by omega)
  rw [show home K n - 1 - (K - k - 1) = cell K n 0 k by rw [hh]; unfold cell; omega] at h2
  have h3 := seg_scanUp (C := C) (kin := kin) (Sp := Sp) (n := n) S hk act cont
    (by unfold cell at hSp ⊢; omega) (S k).length 0 (by simp)
  simp only [decide_true] at h3
  exact ((h1.trans h2).trans h3).of_eq (by ring)

/-! ### One instruction -/

theorem lay_blank {n : ℕ} (S : Store) {k : ℕ} (hk : k < K) :
    lay K n S (cell K n (S k).length k) = none := by
  rw [lay_track _ hk]; simp

theorem lay_top {n : ℕ} (S : Store) {k : ℕ} (hk : k < K) {c : Bool} {rest : List Bool}
    (hS : S k = c :: rest) : lay K n S (cell K n rest.length k) = some c := by
  rw [lay_track _ hk, hS]; simp

theorem nxt_write {c : Config QS Sym} {q : QS} {m : Move} {γ : Sym} :
    nxt c (q, γ, m) = ⟨q, m.apply c.head, Function.update c.tape c.head γ⟩ := rfl

/-- After writing at the first blank cell (push, guess), finishing gives the new store. -/
theorem seg_push_tail {Sp n : ℕ} (S : Store) {k : ℕ} (hk : k < K) (b : Bool) (cont : Option ℕ)
    (hSp : cell K n (S k).length K < Sp) :
    (simM C K kin).Seg Sp
      (nxt ⟨QS.base (.scan .guess k cont (decide ((S k).length = 0))), cell K n (S k).length k,
        lay K n S⟩ (mvTo true (K - k) (.rScan cont), some b, .stay))
      ⟨.base (contPh cont), home K n, lay K n (Function.update S k (b :: S k))⟩
      ((K - k) + ((S k).length * (K + 1) + 1)) := by
  simp only [nxt_write, Move.apply]
  rw [lay_push S hk b]
  have := seg_finish (C := C) (kin := kin) (Sp := Sp) (n := n)
    (Function.update S k (b :: S k)) hk cont (S k).length hSp
  exact this

/-- **Push.** -/
theorem seg_push {Sp n pc k : ℕ} {b : Bool} (S : Store) (hpc : C[pc]? = some (.push k b))
    (hk : k < K) (hSp : cell K n ((S k).length) K < Sp) :
    (simM C K kin).Seg Sp (good K n ⟨pc, S⟩) (good K n ⟨pc + 1, Function.update S k (b :: S k)⟩)
      ((1 + (K - k - 1) + (S k).length * (K + 1)) + 1 + ((K - k) + ((S k).length * (K + 1) + 1))) := by
  have h1 := seg_start (C := C) (kin := kin) (Sp := Sp) (n := n) (pc := pc) S hk (.push b)
    (some (pc + 1)) (fun γ => by simp [execTr, hpc]) (by rw [hpc]; simp) hSp
  have hb := lay_blank (n := n) S hk
  have h2 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
    (c := ⟨.base (.scan (.push b) k (some (pc + 1)) (decide ((S k).length = 0))),
      cell K n (S k).length k, lay K n S⟩)
    (t := (mvTo true (K - k) (.rScan (some (pc + 1))), some b, .stay))
    (by simp only; rw [hb]; rfl) (notAcc_base (by intro pc h; cases h))
    (show cell K n (S k).length k < Sp by unfold cell at hSp ⊢; omega)
    (show cell K n (S k).length k < Sp by unfold cell at hSp ⊢; omega)
  simp only [nxt_write, Move.apply] at h2
  rw [lay_push S hk b] at h2
  have h3 := seg_finish (C := C) (kin := kin) (Sp := Sp) (n := n)
    (Function.update S k (b :: S k)) hk (some (pc + 1)) (S k).length hSp
  exact (h1.trans h2).trans h3

/-- **Guess**, up to the choice. -/
theorem seg_guess_pre {Sp n pc k : ℕ} (S : Store) (hpc : C[pc]? = some (.guess k))
    (hk : k < K) (hSp : cell K n ((S k).length) K < Sp) :
    (simM C K kin).Seg Sp (good K n ⟨pc, S⟩)
      ⟨QS.base (.scan .guess k (some (pc + 1)) (decide ((S k).length = 0))), cell K n (S k).length k,
        lay K n S⟩
      (1 + (K - k - 1) + (S k).length * (K + 1)) :=
  seg_start (C := C) (kin := kin) (Sp := Sp) (n := n) (pc := pc) S hk .guess
    (some (pc + 1)) (fun γ => by simp [execTr, hpc]) (by rw [hpc]; simp) hSp

theorem δ_guess {n k : ℕ} (S : Store) (hk : k < K) (cont : Option ℕ) (first : Bool) :
    δ C K kin (QS.base (.scan .guess k cont first)) (lay K n S (cell K n (S k).length k)) =
      [(mvTo true (K - k) (.rScan cont), some false, .stay),
        (mvTo true (K - k) (.rScan cont), some true, .stay)] := by
  rw [lay_blank S hk]; rfl

/-- **Pop.** -/
theorem seg_pop {Sp n pc k : ℕ} (S : Store) (hpc : C[pc]? = some (.pop k))
    (hk : k < K) (hSp : cell K n ((S k).length) K < Sp) :
    ∃ m, (simM C K kin).Seg Sp (good K n ⟨pc, S⟩)
      (good K n ⟨pc + 1, Function.update S k (S k).tail⟩) m ∧ 1 ≤ m ∧
      m ≤ 3 * ((S k).length + 2) * (K + 1) := by
  have h1 := seg_start (C := C) (kin := kin) (Sp := Sp) (n := n) (pc := pc) S hk .pop
    (some (pc + 1)) (fun γ => by simp [execTr, hpc]) (by rw [hpc]; simp) hSp
  have hb := lay_blank (n := n) S hk
  rcases hS : S k with _ | ⟨c, rest⟩
  · -- empty stack: nothing to do
    simp only [hS, List.length_nil, decide_true] at h1 hb hSp
    have h2 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.scan .pop k (some (pc + 1)) true), cell K n 0 k, lay K n S⟩)
      (t := (mvTo true (K - k) (.rScan (some (pc + 1))), none, .stay))
      (by simp only; rw [show lay K n S (cell K n 0 k) = none from hb]; rfl)
      (notAcc_base (by intro pc h; cases h))
      (show cell K n 0 k < Sp by unfold cell at hSp ⊢; omega)
      (show cell K n 0 k < Sp by unfold cell at hSp ⊢; omega)
    rw [nxt_same' hb] at h2
    simp only [Move.apply] at h2
    have h3 := seg_finish (C := C) (kin := kin) (Sp := Sp) (n := n) S hk (some (pc + 1)) 0 hSp
    rw [show Function.update S k ([] : List Bool).tail = S from
      Function.update_eq_self_iff.2 (by rw [hS]; rfl)]
    have hx := Nat.sub_le K k
    exact ⟨_, (h1.trans h2).trans h3, by omega, by simp; omega⟩
  · simp only [hS, List.length_cons, show decide (rest.length + 1 = 0) = false by simp] at h1 hb hSp
    have h2 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.scan .pop k (some (pc + 1)) false), cell K n (rest.length + 1) k, lay K n S⟩)
      (t := (mvTo false K (.top .pop k (some (pc + 1))), none, .left))
      (by simp only; rw [show lay K n S (cell K n (rest.length + 1) k) = none from hb]; rfl)
      (notAcc_base (by intro pc h; cases h))
      (show cell K n (rest.length + 1) k < Sp by unfold cell at hSp ⊢; omega)
      (show cell K n (rest.length + 1) k - 1 < Sp by unfold cell at hSp ⊢; omega)
    rw [nxt_same' hb] at h2
    simp only [Move.apply] at h2
    have h3 := seg_mvTo_left (C := C) (K := K) (kin := kin) (Sp := Sp) (.top .pop k (some (pc + 1)))
      (lay K n S) K (cell K n (rest.length + 1) k - 1) (by rw [cell_succ]; omega)
      (by unfold cell at hSp ⊢; omega)
    rw [show cell K n (rest.length + 1) k - 1 - K = cell K n rest.length k by rw [cell_succ]; omega]
      at h3
    have ht := lay_top (n := n) S hk hS
    have h4 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.top .pop k (some (pc + 1))), cell K n rest.length k, lay K n S⟩)
      (t := (mvTo true (K - k) (.rScan (some (pc + 1))), none, .stay))
      (by simp only; rw [ht]; rfl) (notAcc_base (by intro pc h; cases h))
      (show cell K n rest.length k < Sp by unfold cell at hSp ⊢; nlinarith)
      (show cell K n rest.length k < Sp by unfold cell at hSp ⊢; nlinarith)
    simp only [nxt_write, Move.apply] at h4
    rw [lay_pop S hk hS] at h4
    have h5 := seg_finish (C := C) (kin := kin) (Sp := Sp) (n := n) (Function.update S k rest) hk
      (some (pc + 1)) rest.length (by unfold cell at hSp ⊢; nlinarith)
    simp only [List.tail_cons, List.length_cons]
    refine ⟨_, (((h1.trans h2).trans h3).trans h4).trans h5, by omega, ?_⟩
    have hx : K - k - 1 ≤ K := by omega
    have hy : K - k ≤ K := by omega
    have e : (rest.length + 1) * (K + 1) = rest.length * (K + 1) + (K + 1) := by ring
    have e2 : 3 * (rest.length + 1 + 2) * (K + 1) = 3 * (rest.length * (K + 1)) + 9 * (K + 1) := by
      ring
    rw [e, e2]
    omega

/-- **Branch.** -/
theorem seg_br {Sp n pc k a₀ aF aT : ℕ} (S : Store) (hpc : C[pc]? = some (.br k a₀ aF aT))
    (hk : k < K) (hSp : cell K n ((S k).length) K < Sp) :
    ∃ m, (simM C K kin).Seg Sp (good K n ⟨pc, S⟩)
      (good K n ⟨match S k with | [] => a₀ | false :: _ => aF | true :: _ => aT, S⟩) m ∧ 1 ≤ m ∧
      m ≤ 3 * ((S k).length + 2) * (K + 1) := by
  have h1 := seg_start (C := C) (kin := kin) (Sp := Sp) (n := n) (pc := pc) S hk (.br a₀ aF aT)
    none (fun γ => by simp [execTr, hpc]) (by rw [hpc]; simp) hSp
  have hb := lay_blank (n := n) S hk
  rcases hS : S k with _ | ⟨c, rest⟩
  · simp only [hS, List.length_nil, decide_true] at h1 hb hSp
    have h2 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.scan (.br a₀ aF aT) k none true), cell K n 0 k, lay K n S⟩)
      (t := (mvTo true (K - k) (.rScan (some a₀)), none, .stay))
      (by simp only; rw [show lay K n S (cell K n 0 k) = none from hb]; rfl)
      (notAcc_base (by intro pc h; cases h))
      (show cell K n 0 k < Sp by unfold cell at hSp ⊢; omega)
      (show cell K n 0 k < Sp by unfold cell at hSp ⊢; omega)
    rw [nxt_same' hb] at h2
    simp only [Move.apply] at h2
    have h3 := seg_finish (C := C) (kin := kin) (Sp := Sp) (n := n) S hk (some a₀) 0 hSp
    have hx := Nat.sub_le K k
    exact ⟨_, (h1.trans h2).trans h3, by omega, by simp; omega⟩
  · simp only [hS, List.length_cons, show decide (rest.length + 1 = 0) = false by simp] at h1 hb hSp
    have h2 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.scan (.br a₀ aF aT) k none false), cell K n (rest.length + 1) k, lay K n S⟩)
      (t := (mvTo false K (.top (.br a₀ aF aT) k none), none, .left))
      (by simp only; rw [show lay K n S (cell K n (rest.length + 1) k) = none from hb]; rfl)
      (notAcc_base (by intro pc h; cases h))
      (show cell K n (rest.length + 1) k < Sp by unfold cell at hSp ⊢; omega)
      (show cell K n (rest.length + 1) k - 1 < Sp by unfold cell at hSp ⊢; omega)
    rw [nxt_same' hb] at h2
    simp only [Move.apply] at h2
    have h3 := seg_mvTo_left (C := C) (K := K) (kin := kin) (Sp := Sp) (.top (.br a₀ aF aT) k none)
      (lay K n S) K (cell K n (rest.length + 1) k - 1) (by rw [cell_succ]; omega)
      (by unfold cell at hSp ⊢; omega)
    rw [show cell K n (rest.length + 1) k - 1 - K = cell K n rest.length k by rw [cell_succ]; omega]
      at h3
    have ht := lay_top (n := n) S hk hS
    have h4 := seg_det (C := C) (K := K) (kin := kin) (Sp := Sp)
      (c := ⟨.base (.top (.br a₀ aF aT) k none), cell K n rest.length k, lay K n S⟩)
      (t := (mvTo true (K - k) (.rScan (some (if c then aT else aF))), some c, .stay))
      (by simp only; rw [ht]; rfl) (notAcc_base (by intro pc h; cases h))
      (show cell K n rest.length k < Sp by unfold cell at hSp ⊢; nlinarith)
      (show cell K n rest.length k < Sp by unfold cell at hSp ⊢; nlinarith)
    rw [nxt_same' ht] at h4
    simp only [Move.apply] at h4
    have h5 := seg_finish (C := C) (kin := kin) (Sp := Sp) (n := n) S hk
      (some (if c then aT else aF)) rest.length (by unfold cell at hSp ⊢; nlinarith)
    have hall := (((h1.trans h2).trans h3).trans h4).trans h5
    have hx : K - k - 1 ≤ K := by omega
    have hy : K - k ≤ K := by omega
    have e : (rest.length + 1) * (K + 1) = rest.length * (K + 1) + (K + 1) := by ring
    have e2 : 3 * ((c :: rest).length + 2) * (K + 1) = 3 * (rest.length * (K + 1)) + 9 * (K + 1) := by
      simp only [List.length_cons]; ring
    rw [e2]
    rw [e] at hall
    cases c
    · exact ⟨_, hall, by omega, by omega⟩
    · exact ⟨_, hall, by omega, by omega⟩

end Mach

end HTN
