import FondHtn.TOHard2.FBridge
import FondHtn.TOHard2.SoundK
/-!
# Soundness of the claims for fair policies

The fair counterpart of `FondHtn/TOHard2/SoundK.lean`.  A claim `K a` lying in a fair set `Y`
(target `Ψ`) is sound, `FOND.TOHard2.SoundC`, in two steps:

* **coverage** (`FOND.TOHard2.cover_fair`): `Ψ` contains states for every challenged index.  By
  induction on the attractor rank, following the challenge that the attractor uses: the rank
  decreases along that path, and the inner claim's coverage transfers outwards
  (`FOND.TOHard2.transfer`);
* **pinning** (`FOND.TOHard2.pin_fair`): by induction on the time `t` of the claim.  Coverage of
  the inner claims of *all* challenges forces `t = t' + 1` (so a policy cannot keep recursing
  below time `0`), and the inner claims are sound by the induction hypothesis.

The instructions other than the picks of nature have a single effect per alternative
(`FOND.TOHard2.Det`), so the attractor's "some outcome" is "all outcomes" for them
(`FOND.TOHard2.fa_ins_det`).
-/

set_option linter.unusedSimpArgs false

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

/-! ## Deterministic instructions and picks -/

section Gen

variable {G : Gram} {Ψ : Set Cfg} {Y : List (Bool × ℕ) → Cfg → Prop}

/-- Every alternative has a single effect. -/
def Det (I : List ASpec) : Prop := ∀ a ∈ I, ∃ e, a.effs = [e]

theorem det_tst (alts : List (List ℕ × List ℕ)) : Det (tst alts) := fun a ha => by
  obtain ⟨pn, -, rfl⟩ := List.mem_map.1 ha
  exact ⟨_, rfl⟩

theorem fa_ins_det (hnd : G.InsNodup) {n m : ℕ} {I : List ASpec} (hI : (m, I) ∈ G.insL)
    (hdet : Det I) {xs : List (Bool × ℕ)} {c : Cfg} (h : FA G Ψ Y (n + 1) ((false, m) :: xs) c) :
    c ∈ wpI I {c' | FA G Ψ Y n xs c'} := by
  obtain ⟨a, ha, happ, -, c₀, hc₀, h₀⟩ := fa_ins hnd hI h
  obtain ⟨e, he⟩ := hdet a ha
  refine ⟨a, ha, happ, fun c' hc' => ?_⟩
  obtain ⟨e', he', rfl⟩ := hc'
  obtain ⟨e'', he'', rfl⟩ := hc₀
  rw [he, List.mem_singleton] at he' he''
  subst he' he''
  exact h₀

/-- **A pick of nature**: some picked outcome is in the attractor of lower rank. -/
theorem fa_ins_pick (hnd : G.InsNodup) {n m : ℕ} {sel : ℕ → ℕ} {k : ℕ}
    (hI : (m, pickI sel k) ∈ G.insL) {xs : List (Bool × ℕ)} {c : Cfg}
    (h : FA G Ψ Y (n + 1) ((false, m) :: xs) c) :
    ∃ i < k, Y xs (c.pick sel k i) ∧ FA G Ψ Y n xs (c.pick sel k i) := by
  obtain ⟨a, ha, -, hall, c₀, hc₀, h₀⟩ := fa_ins hnd hI h
  simp only [pickI, List.mem_singleton] at ha
  subst ha
  have hY0 := hall c₀ hc₀
  obtain ⟨e, he, rfl⟩ := hc₀
  simp only [ASpec.effs, List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  refine ⟨i, hi, ?_, ?_⟩
  · convert hY0 using 1
  · convert h₀ using 1

end Gen

/-! ## Chains and challenges in the fair game -/

section Chains

variable (P : Par) {Ψ : Set Cfg} {Y : List (Bool × ℕ) → Cfg → Prop}

theorem fa_ch {A : Comp} {y n : ℕ} {xs : List (Bool × ℕ)} {c : Cfg}
    (h : FA (gram P) Ψ Y n ((true, chN A y) :: xs) c) :
    ∃ as, Run A.aut as A.aut.acc ∧ Y ((true, y) :: syms (chain P.b P.cs as) ++ xs) c ∧
      FA (gram P) Ψ Y n ((true, y) :: syms (chain P.b P.cs as) ++ xs) c := by
  rcases n with _ | n
  · exact absurd h not_fa_zero
  obtain ⟨bs, hb, hYb, h⟩ := fa_comp h
  rw [gram_methL] at hb
  rw [meth_ch P hb] at h hYb
  simp only [chBody, List.cons_append, List.nil_append] at h hYb
  obtain ⟨as, hrun, hY', h'⟩ := fa_lam (G := gram P) (A := A.aut) (lam := fun σ => lamN A σ y)
    (y := y) (blk := block P.b P.cs) (fun σ bs h => lam_sound P σ bs h) h
  have h'' := h'.mono (n' := n + 1) (by omega)
  exact ⟨as, hrun, by simpa [chain, blocks, List.append_assoc] using hY',
    by simpa [chain, blocks, List.append_assoc] using h''⟩

theorem fa_ch2 {A₁ A₂ : Comp} {y n : ℕ} {xs : List (Bool × ℕ)} {c : Cfg}
    (h : FA (gram P) Ψ Y n ((true, chN A₁ (chN A₂ y)) :: xs) c) :
    ∃ as₁ as₂, Run A₁.aut as₁ A₁.aut.acc ∧ Run A₂.aut as₂ A₂.aut.acc ∧
      Y ((true, y) :: syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++ xs) c ∧
      FA (gram P) Ψ Y n ((true, y) :: syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++ xs) c := by
  obtain ⟨as₁, h1, -, h⟩ := fa_ch P h
  rw [List.cons_append] at h
  obtain ⟨as₂, h2, hY, h⟩ := fa_ch P h
  exact ⟨as₁, as₂, h1, h2, by simpa [List.append_assoc] using hY, by simpa [List.append_assoc] using h⟩

theorem y_ch2 (hY : FSet (gram P) Ψ Y) {A₁ A₂ : Comp} {y : ℕ} {xs : List (Bool × ℕ)} {c : Cfg}
    (h : Y ((true, chN A₁ (chN A₂ y)) :: xs) c) :
    ∃ as₁ as₂, Run A₁.aut as₁ A₁.aut.acc ∧ Run A₂.aut as₂ A₂.aut.acc ∧
      Y ((true, y) :: syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++ xs) c ∧
      ∃ n, FA (gram P) Ψ Y n ((true, y) :: syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++ xs) c := by
  obtain ⟨n, hn⟩ := hY _ _ h
  obtain ⟨as₁, as₂, h1, h2, hY', h'⟩ := fa_ch2 P hn
  exact ⟨as₁, as₂, h1, h2, hY', n, h'⟩

/-- The tail of a challenge: the two chains and the instructions after the challenge. -/
def tailP (asI asT : List AT) (postP : List (ℕ × List ASpec)) : List (ℕ × List ASpec) :=
  chain P.b P.cs asI ++ chain P.b P.cs asT ++ postP

/-- **A challenge body** in the fair game: the challenged mode holds, the digit types are
committed, and the inner claim lies in the fair set; along the attractor the rank decreases. -/
theorem fa_mode (hY : FSet (gram P) Ψ Y) (hP : 2 ≤ P.cs.length) {m x n : ℕ} (hm3 : m < 3)
    {postP : List (ℕ × List ASpec)} {s : St}
    (hYs : Y (modeBody m x ++ syms postP) s.cfg) (hn : FA (gram P) Ψ Y n (modeBody m x ++ syms postP) s.cfg) :
    s.val (4 + m) = true ∧ ∃ asT asI, Run (Comp.inc true).aut asT 1 ∧
      Run (modeI m).aut asI (modeI m).aut.acc ∧
      Y ((true, KN x) :: syms (tailP P asI asT postP)) s.cfg ∧
      ∃ n' < n, FA (gram P) Ψ Y n' ((true, KN x) :: syms (tailP P asI asT postP)) s.cfg := by
  rw [modeBody_eq] at hYs hn
  rcases n with _ | n
  · exact absurd hn not_fa_zero
  simp only [List.cons_append, List.nil_append] at hYs hn
  have hm : (assertMI m) ∈ (gram P).insL := by
    apply insRaw_mem_of_mem
    interval_cases m <;> simp
  obtain ⟨hv, hY1⟩ := wp_assertM.1 (y_ins hY (gram_good P).nodup hm hYs)
  obtain ⟨-, hn1⟩ := wp_assertM.1 (fa_ins_det (gram_good P).nodup hm (det_tst _) hn)
  obtain ⟨asT, asI, hT, hI, hY2, hn2⟩ := fa_ch2 P hn1
  refine ⟨hv, asT, asI, hT, hI, by simpa [tailP, List.append_assoc] using hY2, n, by omega,
    by simpa [tailP, List.append_assoc] using hn2⟩

theorem modeI_ok' (hP : 2 ≤ P.cs.length) (m : ℕ) : (modeI m).Ok P.cs.length := modeI_ok P hP m

/-- The inner claim of a challenge, split off: its fair set, its target and the relation of the
target to the outer one. -/
theorem split_claim (hY : FSet (gram P) Ψ Y) (hP : 2 ≤ P.cs.length) {m : ℕ}
    {asT asI : List AT} (hT : Run (Comp.inc true).aut asT 1)
    (hI : Run (modeI m).aut asI (modeI m).aut.acc) {postP : List (ℕ × List ASpec)}
    (hpost : ∀ q ∈ postP, q ∈ (gram P).insL) :
    FSet (gram P) {c | Y (syms (tailP P asI asT postP)) c}
        (fun u c => Y (u ++ syms (tailP P asI asT postP)) c) ∧
      ∀ s', Shaped s' → s'.cfg ∈ {c | Y (syms (tailP P asI asT postP)) c} →
        s'.cfg ∈ wpP (inss (chain P.b P.cs asI ++ chain P.b P.cs asT)) (wpP (inss postP) Ψ) := by
  refine ⟨fset_split hY _, fun s' _ h' => ?_⟩
  have hmem : ∀ q ∈ tailP P asI asT postP, q ∈ (gram P).insL := by
    intro q hq
    simp only [tailP, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact chain_mem P (run_ok (modeI_ok P hP m) hI) q hq
    · exact chain_mem P (run_ok (by trivial) hT) q hq
    · exact hpost q hq
  have h1 := y_prog hY (gram_good P).nodup hmem (xs := []) (by simpa using h')
  have h2 := wpP_mono _ (fun c hc => y_nil hY hc) h1
  simpa only [tailP, inss_append, wpP_append] using h2

end Chains

/-! ## The claims -/

section Claims

variable {P : Par} {d : TabData} {tabC : ℕ → ℕ → ℕ} (H : Hyp P d tabC)

/-- The bodies of a challenge nonterminal. -/
theorem sub_shape {k j : ℕ} {bs : List (Bool × ℕ)} (hb : (subN k j, bs) ∈ meths P) :
    ∃ mm < 3, ∃ x, ∃ postP : List (ℕ × List ASpec), (postP = [] ∨ ∃ β, postP = [assertIBI β]) ∧
      bs = modeBody mm x ++ syms postP := by
  rcases meth_sub P hb with ⟨-, -, rfl | rfl | rfl⟩ | ⟨-, -, rfl | rfl⟩ | ⟨-, -, rfl | rfl⟩
  · exact ⟨0, by norm_num, (P.mid.getI j).2.1, [], Or.inl rfl, by simp⟩
  · exact ⟨1, by norm_num, (P.mid.getI j).2.2.1, [], Or.inl rfl, by simp⟩
  · exact ⟨2, by norm_num, (P.mid.getI j).2.2.2, [], Or.inl rfl, by simp⟩
  · exact ⟨1, by norm_num, (P.lft.getI j).2.1, [assertIBI false], Or.inr ⟨false, rfl⟩, by simp⟩
  · exact ⟨2, by norm_num, (P.lft.getI j).2.2, [assertIBI false], Or.inr ⟨false, rfl⟩, by simp⟩
  · exact ⟨0, by norm_num, (P.rgt.getI j).2.1, [assertIBI true], Or.inr ⟨true, rfl⟩, by simp⟩
  · exact ⟨1, by norm_num, (P.rgt.getI j).2.2, [assertIBI true], Or.inr ⟨true, rfl⟩, by simp⟩

theorem post_mem {postP : List (ℕ × List ASpec)} (h : postP = [] ∨ ∃ β, postP = [assertIBI β]) :
    ∀ q ∈ postP, q ∈ (gram P).insL := by
  rcases h with rfl | ⟨β, rfl⟩
  · simp
  · intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact insRaw_mem_of_mem P (by cases β <;> simp)

theorem reg_modeI {m : ℕ} {asI : List AT} (hI : Run (modeI m).aut asI (modeI m).aut.acc) :
    ∀ a ∈ asI, a = .id ∨ a.reg = false := by
  have := run_reg hI
  intro a ha; rcases this a ha with h | h
  · exact Or.inl h
  · right; rw [h]; unfold modeI; split_ifs <;> rfl

/-- Coverage of the claims won with attractor rank `n`. -/
def CovS (P : Par) (n : ℕ) : Prop :=
  ∀ a (s : St) (Ψ : Set Cfg) (Y : List (Bool × ℕ) → Cfg → Prop), FSet (gram P) Ψ Y →
    Y [(true, KN a)] s.cfg → FA (gram P) Ψ Y n [(true, KN a)] s.cfg → Shaped s → Cover P Ψ

/-- Pinning of the claims with time below `T`. -/
def PinS (P : Par) (tabC : ℕ → ℕ → ℕ) (T : ℕ) : Prop :=
  ∀ a (s : St) (Ψ : Set Cfg) (Y : List (Bool × ℕ) → Cfg → Prop), FSet (gram P) Ψ Y →
    Y [(true, KN a)] s.cfg → Shaped s → ∀ tg ig, Pin P Ψ tg ig → ofB tg (2 ^ P.b) < T →
      tabC (ofB tg (2 ^ P.b)) (ofB ig (2 ^ P.b)) = a

include H

/-- **A challenge, coverage**: along the attractor, the inner claim has lower rank. -/
theorem sub_cover {n k j : ℕ} (ih : ∀ n' < n, CovS P n') {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    {Y : List (Bool × ℕ) → Cfg → Prop} (hY : FSet (gram P) Ψ Y) (hYs : Y [(true, subN k j)] s.cfg)
    (hn : FA (gram P) Ψ Y n [(true, subN k j)] s.cfg) : Cover P Ψ := by
  rcases n with _ | n
  · exact absurd hn not_fa_zero
  obtain ⟨bs, hb, hYb, hnb⟩ := fa_comp hn
  rw [gram_methL] at hb
  obtain ⟨mm, hmm, x, postP, hpostP, rfl⟩ := sub_shape hb
  rw [List.append_nil] at hYb hnb
  obtain ⟨-, asT, asI, hT, hI, hYi, n', hn', hni⟩ := fa_mode P hY H.two_le hmm hYb hnb
  obtain ⟨hFS, hrel⟩ := split_claim P hY H.two_le hT hI (post_mem hpostP)
  have hni' := fa_split (ys := syms (tailP P asI asT postP)) hni (xs := [(true, KN x)]) rfl hYi
  have hcov := ih n' (by omega) x s _ _ hFS hYi hni' hs
  obtain ⟨hcov', -⟩ := transfer H.cs (run_reg hT) (reg_modeI hI) hrel hcov
  rcases hpostP with rfl | ⟨β, rfl⟩
  · simpa using hcov'
  · exact (post_IB H hcov').1

/-! ### The first row -/

/-- **A prefix cell** (fair). -/
theorem sound_prefF {a c : ℕ} (hc : c < P.baseU.length) (ha : P.baseU.getI c = a) {s : St}
    (hs : Shaped s) {Ψ : Set Cfg} {Y : List (Bool × ℕ) → Cfg → Prop} (hY : FSet (gram P) Ψ Y)
    (h : Y (prefBody P c ++ []) s.cfg) : SoundC P tabC a Ψ := by
  have hok : (AT.ce (2 + c)).Ok P.cs.length := by show 2 + c < P.cs.length; rw [H.csl]; omega
  have hp : ∀ q ∈ pickChks P ++ [clrTBI, guessIBI, setEQ] ++ actP P.b P.cs (.ce (2 + c)),
      q ∈ (gram P).insL := by
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact pickChks_mem P q hq
    · exact insRaw_mem_of_mem P (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                                    rcases hq with rfl | rfl | rfl <;> simp)
    · exact actP_mem P hok q hq
  have hw := y_prog hY (gram_good P).nodup hp (xs := [])
    (show Y (syms (pickChks P ++ [clrTBI, guessIBI, setEQ] ++ actP P.b P.cs (.ce (2 + c)))
      ++ []) s.cfg by simpa [prefBody] using h)
  replace hw := wpP_mono _ (fun c' hc' => y_nil hY hc') hw
  simp only [inss_append, wpP_append, wp_pickChks] at hw
  have key : ∀ k < 2 ^ P.b, ∃ s', Shaped s' ∧ s'.chkV P.b = k ∧ s'.cfg ∈ Ψ ∧
      (s'.tb = false ∧ s'.ib = kDig P.cs (2 + c) k) := by
    intro k hk
    have h1 := hw k.testBit
    simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_clrTB, wp_guessIB, wp_setEQ] at h1
    obtain ⟨v, -, h1⟩ := h1
    rw [wp_act H.cs] at h1
    simp only [if_true] at h1
    obtain ⟨v', hrho, h1⟩ := h1
    have hk' := chkV_pick_testBit P s hk
    simp only [AT.reg, St.reg, St.setReg, Bool.false_eq_true, if_false, rho_ce] at hrho h1
    simp only [St.chkV, ofB_pick_testBit P s.chk hk] at hrho
    refine ⟨_, ?_, ?_, h1, rfl, ?_⟩
    · exact hs
    · exact hk'
    · simp only [kDig]; rw [hrho.2, hrho.1]
  obtain ⟨hcov, hpin⟩ := pin_of key
  refine ⟨hcov, fun tg ig hp' => ?_⟩
  have hd := hpin tg ig hp'
  have ht : ofB tg (2 ^ P.b) = 0 := ofB_eq_zero fun k hk => by
    obtain ⟨s', ⟨e1, -⟩, e2, -⟩ := hd k hk; rw [← e2, e1]
  have hi : ofB ig (2 ^ P.b) = c := by
    rw [← H.kc c hc]
    exact ofB_congr fun k hk => by obtain ⟨s', ⟨-, e1⟩, -, e2⟩ := hd k hk; rw [← e2, e1]
  rw [ht, hi, H.good.base c (by rw [H.c₁]; exact hc), ← H.baseU, ha]

/-- **The first row after the prefix** (fair). -/
theorem sound_bbF {A₁ A₂ : Comp} (hA₁ : A₁.Check) (hA₂ : A₂.Check) (hok₁ : A₁.Ok P.cs.length)
    (hok₂ : A₂.Ok P.cs.length) {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    {Y : List (Bool × ℕ) → Cfg → Prop} (hY : FSet (gram P) Ψ Y)
    (h : Y [(true, chN A₁ (chN A₂ bbN))] s.cfg) :
    ∃ as₁ as₂, Run A₁.aut as₁ A₁.aut.acc ∧ Run A₂.aut as₂ A₂.aut.acc ∧ as₁.length = 2 ^ P.b ∧
      as₂.length = 2 ^ P.b ∧ Cover P Ψ ∧ ∀ tg ig, Pin P Ψ tg ig →
        ofB tg (2 ^ P.b) = 0 ∧ Rel P.cs as₁ ig ig ∧ Rel P.cs as₂ ig ig := by
  obtain ⟨as₁, as₂, hr₁, hr₂, h, -⟩ := y_ch2 P hY h
  obtain ⟨bs, hb, h⟩ := y_comp hY h
  rw [gram_methL] at hb
  rw [meth_bb P hb] at h
  have hp : ∀ q ∈ pickChks P ++ [clrTBI, guessIBI] ++ chain P.b P.cs as₂ ++ chain P.b P.cs as₁,
      q ∈ (gram P).insL := by
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((hq | hq) | hq) | hq
    · exact pickChks_mem P q hq
    · exact insRaw_mem_of_mem P (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                                    rcases hq with rfl | rfl <;> simp)
    · exact chain_mem P (run_ok hok₂ hr₂) q hq
    · exact chain_mem P (run_ok hok₁ hr₁) q hq
  have hw := y_prog hY (gram_good P).nodup hp (xs := [])
    (show Y (syms (pickChks P ++ [clrTBI, guessIBI] ++ chain P.b P.cs as₂ ++
      chain P.b P.cs as₁) ++ []) s.cfg by simpa [bbBody, List.append_assoc] using h)
  replace hw := wpP_mono _ (fun c' hc' => y_nil hY hc') hw
  simp only [inss_append, wpP_append, wp_pickChks] at hw
  have hreg₁ : ∀ a ∈ as₁, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hr₁ a ha with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (Comp.reg_of_check hA₁))
  have hreg₂ : ∀ a ∈ as₂, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hr₂ a ha with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (Comp.reg_of_check hA₂))
  have key : ∀ g : ℕ → Bool, as₂.length = 2 ^ P.b ∧ as₁.length = 2 ^ P.b ∧ ∃ s', Shaped s' ∧
      s'.chkV P.b = ofB g P.b ∧ s'.cfg ∈ Ψ ∧ s'.tb = false ∧
      (as₂.getD (ofB g P.b) .id).rho P.cs (ofB g P.b) s'.ib = some s'.ib ∧
      (as₁.getD (ofB g P.b) .id).rho P.cs (ofB g P.b) s'.ib = some s'.ib := by
    intro g
    have h1 := hw g
    simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_clrTB, wp_guessIB] at h1
    obtain ⟨v, h1⟩ := h1
    rw [← wpP_append, ← inss_append] at h1
    obtain ⟨hl₂, hl₁, v₂, v₁, h2, h3, h4⟩ := (wp_chain2I H.cs hreg₁ hreg₂
      (show Shaped { s with chk := fun r => if r < P.b then g r else s.chk r, tb := false, ib := v }
        from hs)).1 h1
    have hck : ({ s with chk := fun r => if r < P.b then g r else s.chk r, tb := false, ib := v } :
        St).chkV P.b = ofB g P.b := chkV_pick P _ g
    rw [hck] at h2 h3
    have hlt : ofB g P.b < as₂.length := hl₂ ▸ ofB_lt _ _
    have hlt' : ofB g P.b < as₁.length := hl₁ ▸ ofB_lt _ _
    have e2 := run_check hA₂ hr₂ hlt h2
    subst e2
    have e1 := run_check hA₁ hr₁ hlt' h3
    subst e1
    refine ⟨hl₂, hl₁, _, shaped_fn _, ?_, h4, rfl, h2, h3⟩
    exact hck
  obtain ⟨hl₂, hl₁, -⟩ := key fun _ => false
  have key' : ∀ k < 2 ^ P.b, ∃ s', Shaped s' ∧ s'.chkV P.b = k ∧ s'.cfg ∈ Ψ ∧ (s'.tb = false ∧
      (as₂.getD k .id).rho P.cs k s'.ib = some s'.ib ∧ (as₁.getD k .id).rho P.cs k s'.ib = some s'.ib) := by
    intro k hk
    obtain ⟨-, -, s', hs', hk', h1, h2, h3, h4⟩ := key k.testBit
    rw [ofB_testBit hk] at hk' h3 h4
    exact ⟨s', hs', hk', h1, h2, h3, h4⟩
  obtain ⟨hcov, hpin⟩ := pin_of key'
  refine ⟨as₁, as₂, hr₁, hr₂, hl₁, hl₂, hcov, fun tg ig hp' => ?_⟩
  have hd := hpin tg ig hp'
  refine ⟨ofB_eq_zero fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨s', ⟨e1, -⟩, e2, -⟩ := hd k hk; rw [← e2, e1]
  · obtain ⟨s', ⟨-, -, e1⟩, -, e2⟩ := hd k (hl₁ ▸ hk); rw [← e2]; exact e1
  · obtain ⟨s', ⟨-, e1, -⟩, -, e2⟩ := hd k (hl₂ ▸ hk); rw [← e2]; exact e1

/-- **The cells holding `1`** (fair). -/
theorem sound_trueF {s : St} (hs : Shaped s) {Ψ : Set Cfg} {Y : List (Bool × ℕ) → Cfg → Prop}
    (hY : FSet (gram P) Ψ Y) (h : Y [(true, chN (.cmp 0 true) (chN (.cmp 1 false) bbN))] s.cfg) :
    SoundC P tabC P.codeTrue Ψ := by
  have h2 := H.two_le
  obtain ⟨as₁, as₂, hr₁, hr₂, hl₁, hl₂, hcov, hres⟩ := sound_bbF H (A₁ := .cmp 0 true)
    (A₂ := .cmp 1 false) trivial trivial (show 0 < P.cs.length by omega)
    (show 1 < P.cs.length by omega) hs hY h
  refine ⟨hcov, fun tg ig hp => ?_⟩
  obtain ⟨ht, hR₁, hR₂⟩ := hres tg ig hp
  obtain ⟨-, hσ₁, -⟩ := run_cmp hr₁ hR₁
  obtain ⟨-, hσ₂, -⟩ := run_cmp hr₂ hR₂
  simp only [Comp.aut, Bool.toNat_true, Bool.toNat_false, true_iff, zero_ne_one, false_iff,
    not_le, hl₁, hl₂, H.k0, H.k1] at hσ₁ hσ₂
  rw [ht, H.good.tru _ hσ₁ hσ₂, H.codeTrue]

/-- **The blank cells** (fair). -/
theorem sound_noneF {s : St} (hs : Shaped s) {Ψ : Set Cfg} {Y : List (Bool × ℕ) → Cfg → Prop}
    (hY : FSet (gram P) Ψ Y) (h : Y [(true, chN (.cmp 1 true) (chN .cpy bbN))] s.cfg) :
    SoundC P tabC P.codeNone Ψ := by
  have h2 := H.two_le
  obtain ⟨as₁, as₂, hr₁, hr₂, hl₁, hl₂, hcov, hres⟩ := sound_bbF H (A₁ := .cmp 1 true) (A₂ := .cpy)
    trivial trivial (show 1 < P.cs.length by omega) trivial hs hY h
  refine ⟨hcov, fun tg ig hp => ?_⟩
  obtain ⟨ht, hR₁, -⟩ := hres tg ig hp
  obtain ⟨-, hσ₁, -⟩ := run_cmp hr₁ hR₁
  simp only [Comp.aut, Bool.toNat_true, true_iff, hl₁, H.k1] at hσ₁
  have hlt := ofB_lt ig (2 ^ P.b)
  rw [ht, H.good.non _ hσ₁ (by rw [H.hB]; exact hlt), H.codeNone]

/-! ### Coverage -/

theorem pick3_mem : (pick3I.1, pickI (fun i => 4 + i) 3) ∈ (gram P).insL :=
  insRaw_mem_of_mem P (q := pick3I) (by simp)
theorem pickCR_mem : (pickCRI.1, pickI (fun i => 5 + i) 2) ∈ (gram P).insL :=
  insRaw_mem_of_mem P (q := pickCRI) (by simp)
theorem pickLC_mem : (pickLCI.1, pickI (fun i => 4 + i) 2) ∈ (gram P).insL :=
  insRaw_mem_of_mem P (q := pickLCI) (by simp)

/-- **Coverage of the claims**, by induction on the attractor rank. -/
theorem cover_fair : ∀ n, CovS P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a s Ψ Y hY hYs hn hs
  rcases n with _ | n
  · exact absurd hn not_fa_zero
  obtain ⟨bs, hb, hYb, hnb⟩ := fa_comp hn
  rw [gram_methL] at hb
  rcases meth_K P hb with ⟨j, hj, ha, rfl⟩ | ⟨j, hj, ha, rfl⟩ | ⟨j, hj, ha, rfl⟩ | ⟨c, hc, ha, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [List.cons_append, List.nil_append] at hYb hnb
    rcases n with _ | n
    · exact absurd hnb not_fa_zero
    obtain ⟨i, hi, hYi, hni⟩ := fa_ins_pick (gram_good P).nodup (pick3_mem H) hnb
    rw [pick_cfg s (by norm_num) (by norm_num) hi] at hYi hni
    exact sub_cover H (fun n' hn' => ih n' (by omega)) (shaped_modeSt hs _ _ _) hY hYi hni
  · simp only [List.cons_append, List.nil_append] at hYb hnb
    rcases n with _ | n
    · exact absurd hnb not_fa_zero
    obtain ⟨i, hi, hYi, hni⟩ := fa_ins_pick (gram_good P).nodup (pickCR_mem H) hnb
    rw [pick_cfg s (by norm_num) (by norm_num) hi] at hYi hni
    exact sub_cover H (fun n' hn' => ih n' (by omega)) (shaped_modeSt hs _ _ _) hY hYi hni
  · simp only [List.cons_append, List.nil_append] at hYb hnb
    rcases n with _ | n
    · exact absurd hnb not_fa_zero
    obtain ⟨i, hi, hYi, hni⟩ := fa_ins_pick (gram_good P).nodup (pickLC_mem H) hnb
    rw [pick_cfg s (by norm_num) (by norm_num) hi] at hYi hni
    exact sub_cover H (fun n' hn' => ih n' (by omega)) (shaped_modeSt hs _ _ _) hY hYi hni
  · exact (sound_prefF H hc ha hs hY hYb).1
  · exact (sound_trueF H hs hY (by simpa using hYb)).1
  · exact (sound_noneF H hs hY (by simpa using hYb)).1

theorem cover_of_mem {a : ℕ} {s : St} {Ψ : Set Cfg} {Y : List (Bool × ℕ) → Cfg → Prop}
    (hY : FSet (gram P) Ψ Y) (hYs : Y [(true, KN a)] s.cfg) (hs : Shaped s) : Cover P Ψ := by
  obtain ⟨n, hn⟩ := hY _ _ hYs
  exact cover_fair H n a s Ψ Y hY hYs hn hs

/-! ### Pinning -/

/-- **A challenge, pinning**: coverage of the inner claim forces `t = t' + 1`, and the inner
claim is sound by the induction hypothesis on the time. -/
theorem pick_modeF {T : ℕ} (ihT : PinS P tabC T) {k j mm : ℕ} {X : ℕ → ℕ}
    {postP : List (ℕ × List ASpec)} (hpost : ∀ q ∈ postP, q ∈ (gram P).insL) {s : St} (hs : Shaped s)
    (hbodies : ∀ bs, (subN k j, bs) ∈ meths P → ∃ mm' < 3, bs = modeBody mm' (X mm') ++ syms postP ∧
      (s.val (4 + mm') = true → mm' = mm))
    {Ψ : Set Cfg} {Y : List (Bool × ℕ) → Cfg → Prop} (hY : FSet (gram P) Ψ Y)
    (hYs : Y [(true, subN k j)] s.cfg) :
    Cover P (wpP (inss postP) Ψ) ∧
      ∀ tg ig, Pin P (wpP (inss postP) Ψ) tg ig → ofB tg (2 ^ P.b) < T + 1 → ∃ t' i',
        ofB tg (2 ^ P.b) = t' + 1 ∧
        (mm = 0 → ofB ig (2 ^ P.b) = i' + 1) ∧ (mm = 1 → ofB ig (2 ^ P.b) = i') ∧
        (mm = 2 → ofB ig (2 ^ P.b) + 1 = i') ∧ i' < 2 ^ 2 ^ P.b ∧ tabC t' i' = X mm := by
  obtain ⟨bs, hb, hYb⟩ := y_comp hY hYs
  rw [gram_methL] at hb
  obtain ⟨mm', hmm', rfl, honly⟩ := hbodies bs hb
  rw [List.append_nil] at hYb
  obtain ⟨n, hn⟩ := hY _ _ hYb
  obtain ⟨hv, asT, asI, hT, hI, hYi, -⟩ := fa_mode P hY H.two_le hmm' hYb hn
  obtain rfl := honly hv
  obtain ⟨hFS, hrel⟩ := split_claim P hY H.two_le hT hI hpost
  have hYi' : (fun u c => Y (u ++ syms (tailP P asI asT postP)) c) [(true, KN (X mm'))] s.cfg := hYi
  have hcov := cover_of_mem H hFS hYi' hs
  obtain ⟨hcov', hl₁, hl₂, htr⟩ := transfer H.cs (run_reg hT) (reg_modeI hI) hrel hcov
  refine ⟨hcov', fun tg ig hpin hlt => ?_⟩
  obtain ⟨tg', ig', hpin', hrT, hrI⟩ := htr tg ig hpin
  have hT' := run_inc hT hrT
  simp only [one_ne_zero, if_false, add_zero, hl₁] at hT'
  have hx := ihT (X mm') s _ _ hFS hYi' hs tg' ig' hpin' (by have := hT'.2; omega)
  refine ⟨ofB tg' (2 ^ P.b), ofB ig' (2 ^ P.b), hT'.2, ?_, ?_, ?_, ofB_lt _ _, hx⟩
  · rintro rfl
    have := run_inc (rg := false) (by simpa [modeI] using hI) hrI
    simp only [Comp.aut, one_ne_zero, if_false, add_zero, hl₂] at this
    exact this.2
  · rintro rfl
    have := run_cpy (by simpa [modeI] using hI) hrI
    exact ofB_congr fun r hr => this r (by omega)
  · rintro rfl
    have := run_dec (rg := false) (by simpa [modeI] using hI) hrI
    simp only [Comp.aut, one_ne_zero, if_false, add_zero, hl₂] at this
    exact this.2.symm

/-- Soundness of a claim up to the time `T`. -/
def SoundT (P : Par) (tabC : ℕ → ℕ → ℕ) (T a : ℕ) (Ψ : Set Cfg) : Prop :=
  ∀ tg ig, Pin P Ψ tg ig → ofB tg (2 ^ P.b) < T → tabC (ofB tg (2 ^ P.b)) (ofB ig (2 ^ P.b)) = a

/-- **The middle rule** (fair). -/
theorem sound_midF {T : ℕ} (ihT : PinS P tabC T) {a j : ℕ} (hj : j < P.mid.length)
    (ha : (P.mid.getI j).1 = a) {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    {Y : List (Bool × ℕ) → Cfg → Prop} (hY : FSet (gram P) Ψ Y)
    (h : Y [(false, pick3I.1), (true, subN 0 j)] s.cfg) : SoundT P tabC (T + 1) a Ψ := by
  set q := P.mid.getI j with hq
  have h1 := y_ins (I := pick3I.2) hY (gram_good P).nodup (insRaw_mem_of_mem P (q := pick3I) (by simp)) h
  rw [wp_pick3] at h1
  obtain ⟨hL, hC, hR⟩ := h1
  let X : ℕ → ℕ := fun mm => if mm = 0 then q.2.1 else if mm = 1 then q.2.2.1 else q.2.2.2
  have hb : ∀ (l c r : Bool) (mm : ℕ), (∀ mm' < 3, (modeSt s l c r).val (4 + mm') = true → mm' = mm) →
      ∀ bs, (subN 0 j, bs) ∈ meths P → ∃ mm' < 3, bs = modeBody mm' (X mm') ++ syms [] ∧
        ((modeSt s l c r).val (4 + mm') = true → mm' = mm) := by
    intro l c r mm honly bs hbs
    rcases meth_sub P hbs with ⟨-, -, rfl | rfl | rfl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact ⟨0, by norm_num, by simp [X, hq], honly 0 (by norm_num)⟩
    · exact ⟨1, by norm_num, by simp [X, hq], honly 1 (by norm_num)⟩
    · exact ⟨2, by norm_num, by simp [X, hq], honly 2 (by norm_num)⟩
    · omega
    · omega
  have rL := pick_modeF H ihT (mm := 0) (postP := []) (by simp) (shaped_modeSt hs _ _ _)
    (hb true false false 0 (by intro mm' hmm' hv; interval_cases mm' <;> first | rfl | (simp [modeSt, St.val] at hv))) hY hL
  have rC := pick_modeF H ihT (mm := 1) (postP := []) (by simp) (shaped_modeSt hs _ _ _)
    (hb false true false 1 (by intro mm' hmm' hv; interval_cases mm' <;> first | rfl | (simp [modeSt, St.val] at hv))) hY hC
  have rR := pick_modeF H ihT (mm := 2) (postP := []) (by simp) (shaped_modeSt hs _ _ _)
    (hb false false true 2 (by intro mm' hmm' hv; interval_cases mm' <;> first | rfl | (simp [modeSt, St.val] at hv))) hY hR
  intro tg ig hpin hlt
  obtain ⟨tL, iL, eL1, eL2, -, -, -, hxL⟩ := rL.2 tg ig hpin hlt
  obtain ⟨tC, iC, eC1, -, eC2, -, -, hxC⟩ := rC.2 tg ig hpin hlt
  obtain ⟨tR, iR, eR1, -, -, eR2, hiR, hxR⟩ := rR.2 tg ig hpin hlt
  specialize eL2 rfl; specialize eC2 rfl; specialize eR2 rfl
  simp only [X, if_pos rfl, if_neg (show (1 : ℕ) ≠ 0 by norm_num),
    if_neg (show (2 : ℕ) ≠ 0 by norm_num), if_neg (show (2 : ℕ) ≠ 1 by norm_num)] at hxL hxC hxR
  have hqm : q ∈ d.mid := by
    rw [← H.mid, hq, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hB := H.hB
  have := H.good.mid_s q hqm tC (ofB ig (2 ^ P.b)) (by omega) (by rw [hB]; omega)
    (by rw [show ofB ig (2 ^ P.b) - 1 = iL by omega, show tC = tL by omega]; exact hxL)
    (by rw [eC2]; exact hxC)
    (by rw [eR2, show tC = tR by omega]; exact hxR)
  rw [eC1, this, ← ha]

/-- **Cell `0`** (fair). -/
theorem sound_lftF {T : ℕ} (ihT : PinS P tabC T) {a j : ℕ} (hj : j < P.lft.length)
    (ha : (P.lft.getI j).1 = a) {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    {Y : List (Bool × ℕ) → Cfg → Prop} (hY : FSet (gram P) Ψ Y)
    (h : Y [(false, pickCRI.1), (true, subN 1 j)] s.cfg) : SoundT P tabC (T + 1) a Ψ := by
  set q := P.lft.getI j with hq
  have h1 := y_ins (I := pickCRI.2) hY (gram_good P).nodup (insRaw_mem_of_mem P (q := pickCRI) (by simp)) h
  rw [wp_pickCR] at h1
  obtain ⟨hC, hR⟩ := h1
  let X : ℕ → ℕ := fun mm => if mm = 1 then q.2.1 else q.2.2
  have hpost : ∀ q ∈ [assertIBI false], q ∈ (gram P).insL := by
    intro q hq; exact insRaw_mem_of_mem P (by simp at hq; subst hq; simp)
  have hb : ∀ (l c r : Bool) (mm : ℕ), (∀ mm' < 3, mm' ≠ 0 → (modeSt s l c r).val (4 + mm') = true → mm' = mm) →
      ∀ bs, (subN 1 j, bs) ∈ meths P → ∃ mm' < 3, bs = modeBody mm' (X mm') ++ syms [assertIBI false] ∧
        ((modeSt s l c r).val (4 + mm') = true → mm' = mm) := by
    intro l c r mm honly bs hbs
    rcases meth_sub P hbs with ⟨h0, -⟩ | ⟨-, -, rfl | rfl⟩ | ⟨h0, -⟩
    · omega
    · exact ⟨1, by norm_num, by simp [X, hq], honly 1 (by norm_num) (by norm_num)⟩
    · exact ⟨2, by norm_num, by simp [X, hq], honly 2 (by norm_num) (by norm_num)⟩
    · omega
  have rC := pick_modeF H ihT (mm := 1) hpost (shaped_modeSt hs _ _ _)
    (hb s.ml true false 1 (by intro mm' hmm' h0 hv; interval_cases mm' <;> first | rfl | omega | (simp [modeSt, St.val] at hv))) hY hC
  have rR := pick_modeF H ihT (mm := 2) hpost (shaped_modeSt hs _ _ _)
    (hb s.ml false true 2 (by intro mm' hmm' h0 hv; interval_cases mm' <;> first | rfl | omega | (simp [modeSt, St.val] at hv))) hY hR
  obtain ⟨-, hpost'⟩ := post_IB H rC.1
  intro tg ig hpin hlt
  obtain ⟨hpin', hz⟩ := hpost' tg ig hpin
  have hi0 : ofB ig (2 ^ P.b) = 0 := ofB_eq_zero hz
  obtain ⟨tC, iC, eC1, -, eC2, -, -, hxC⟩ := rC.2 tg ig hpin' hlt
  obtain ⟨tR, iR, eR1, -, -, eR2, -, hxR⟩ := rR.2 tg ig hpin' hlt
  specialize eC2 rfl; specialize eR2 rfl
  simp only [X, if_pos rfl, if_neg (show (2 : ℕ) ≠ 1 by norm_num)] at hxC hxR
  have hqm : q ∈ d.lft := by
    rw [← H.lft, hq, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have := H.good.lft_s q hqm tC (by rw [← hxC, ← eC2, hi0]) (by rw [← hxR, ← eR2, hi0, show tC = tR by omega])
  rw [eC1, hi0, this, ← ha]

/-- **The last cell** (fair). -/
theorem sound_rgtF {T : ℕ} (ihT : PinS P tabC T) {a j : ℕ} (hj : j < P.rgt.length)
    (ha : (P.rgt.getI j).1 = a) {s : St} (hs : Shaped s) {Ψ : Set Cfg}
    {Y : List (Bool × ℕ) → Cfg → Prop} (hY : FSet (gram P) Ψ Y)
    (h : Y [(false, pickLCI.1), (true, subN 2 j)] s.cfg) : SoundT P tabC (T + 1) a Ψ := by
  set q := P.rgt.getI j with hq
  have h1 := y_ins (I := pickLCI.2) hY (gram_good P).nodup (insRaw_mem_of_mem P (q := pickLCI) (by simp)) h
  rw [wp_pickLC] at h1
  obtain ⟨hL, hC⟩ := h1
  let X : ℕ → ℕ := fun mm => if mm = 0 then q.2.1 else q.2.2
  have hpost : ∀ q ∈ [assertIBI true], q ∈ (gram P).insL := by
    intro q hq; exact insRaw_mem_of_mem P (by simp at hq; subst hq; simp)
  have hb : ∀ (l c r : Bool) (mm : ℕ), (∀ mm' < 3, mm' ≠ 2 → (modeSt s l c r).val (4 + mm') = true → mm' = mm) →
      ∀ bs, (subN 2 j, bs) ∈ meths P → ∃ mm' < 3, bs = modeBody mm' (X mm') ++ syms [assertIBI true] ∧
        ((modeSt s l c r).val (4 + mm') = true → mm' = mm) := by
    intro l c r mm honly bs hbs
    rcases meth_sub P hbs with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, -, rfl | rfl⟩
    · omega
    · omega
    · exact ⟨0, by norm_num, by simp [X, hq], honly 0 (by norm_num) (by norm_num)⟩
    · exact ⟨1, by norm_num, by simp [X, hq], honly 1 (by norm_num) (by norm_num)⟩
  have rL := pick_modeF H ihT (mm := 0) hpost (shaped_modeSt hs _ _ _)
    (hb true false s.mr 0 (by intro mm' hmm' h0 hv; interval_cases mm' <;> first | rfl | omega | (simp [modeSt, St.val] at hv))) hY hL
  have rC := pick_modeF H ihT (mm := 1) hpost (shaped_modeSt hs _ _ _)
    (hb false true s.mr 1 (by intro mm' hmm' h0 hv; interval_cases mm' <;> first | rfl | omega | (simp [modeSt, St.val] at hv))) hY hC
  obtain ⟨-, hpost'⟩ := post_IB H rC.1
  intro tg ig hpin hlt
  obtain ⟨hpin', hz⟩ := hpost' tg ig hpin
  have hi1 : ofB ig (2 ^ P.b) + 1 = 2 ^ 2 ^ P.b := ofB_all_true hz
  obtain ⟨tL, iL, eL1, eL2, -, -, -, hxL⟩ := rL.2 tg ig hpin' hlt
  obtain ⟨tC, iC, eC1, -, eC2, -, -, hxC⟩ := rC.2 tg ig hpin' hlt
  specialize eL2 rfl; specialize eC2 rfl
  simp only [X, if_pos rfl, if_neg (show (1 : ℕ) ≠ 0 by norm_num)] at hxL hxC
  have hqm : q ∈ d.rgt := by
    rw [← H.rgt, hq, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hB := H.hB
  have hmx := H.good.hmx
  have htlt := ofB_lt tg (2 ^ P.b)
  have := H.good.rgt_s q hqm tC (by rw [hB]; omega)
    (by rw [hmx, hB, show 2 ^ 2 ^ P.b - 1 - 1 = iL by omega, show tC = tL by omega]; exact hxL)
    (by rw [hmx, hB, show 2 ^ 2 ^ P.b - 1 = iC by omega]; exact hxC)
  rw [eC1, show ofB ig (2 ^ P.b) = d.mx by rw [hmx, hB]; omega, this, ← ha]

/-- **Pinning of the claims**, by induction on the time. -/
theorem pin_fair : ∀ T, PinS P tabC T := by
  intro T
  induction T with
  | zero => intro a s Ψ Y _ _ _ tg ig _ hlt; omega
  | succ T ih =>
    intro a s Ψ Y hY hYs hs tg ig hpin hlt
    obtain ⟨bs, hb, hYb⟩ := y_comp hY hYs
    rw [gram_methL] at hb
    rcases meth_K P hb with ⟨j, hj, ha, rfl⟩ | ⟨j, hj, ha, rfl⟩ | ⟨j, hj, ha, rfl⟩ | ⟨c, hc, ha, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact sound_midF H ih hj ha hs hY (by simpa using hYb) tg ig hpin hlt
    · exact sound_lftF H ih hj ha hs hY (by simpa using hYb) tg ig hpin hlt
    · exact sound_rgtF H ih hj ha hs hY (by simpa using hYb) tg ig hpin hlt
    · exact (sound_prefF H hc ha hs hY hYb).2 tg ig hpin
    · exact (sound_trueF H hs hY (by simpa using hYb)).2 tg ig hpin
    · exact (sound_noneF H hs hY (by simpa using hYb)).2 tg ig hpin

/-- **Soundness of the claims for fair policies.** -/
theorem sound_fair {a : ℕ} {s : St} {Ψ : Set Cfg} {Y : List (Bool × ℕ) → Cfg → Prop}
    (hY : FSet (gram P) Ψ Y) (hYs : Y [(true, KN a)] s.cfg) (hs : Shaped s) : SoundC P tabC a Ψ :=
  ⟨cover_of_mem H hY hYs hs, fun tg ig hpin =>
    pin_fair H (ofB tg (2 ^ P.b) + 1) a s Ψ Y hY hYs hs tg ig hpin (by omega)⟩

/-- **Soundness of the root for fair policies.** -/
theorem root_soundF {Y : List (Bool × ℕ) → Cfg → Prop} (hY : FSet (gram P) Set.univ Y)
    (h : Y [(true, rootN)] s₀.cfg) : ∃ i < 2 ^ d.B, tabC (2 ^ d.B - 1) i ∈ d.acc := by
  obtain ⟨bs, hb, h⟩ := y_comp hY h
  rw [gram_methL] at hb
  obtain ⟨a, ha, rfl⟩ := meth_root P hb
  simp only [List.cons_append, List.nil_append] at h
  obtain ⟨as₁, as₂, hr₁, hr₂, h, -⟩ := y_ch2 P hY h
  set ys := syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁ ++ [assertTBI]) ++ [] with hys
  have h' : (fun u c => Y (u ++ ys) c) [(true, KN a)] s₀.cfg := by
    simpa [hys, List.append_assoc] using h
  obtain ⟨hcov, hsnd⟩ := sound_fair H (fset_split hY ys) h' shaped_s₀
  have hp : ∀ q ∈ chain P.b P.cs as₂ ++ chain P.b P.cs as₁ ++ [assertTBI], q ∈ (gram P).insL := by
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | hq) | rfl
    · exact chain_mem P (run_ok (A := .bits) trivial hr₂) q hq
    · exact chain_mem P (run_ok (A := .cpy) trivial hr₁) q hq
    · exact insRaw_mem_of_mem P (by simp)
  have hreg₁ : ∀ a ∈ as₁, a = .id ∨ a.reg = true := fun a ha => Or.inl (run_cpy_mem hr₁ a ha)
  have hreg₂ : ∀ a ∈ as₂, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hr₂ a ha with h | h
    · exact Or.inl h
    · exact Or.inr h
  let β : ℕ → Bool := fun d => match as₂.getD d .id with
    | .bit b => b
    | _ => false
  have hpost : ∀ s', Shaped s' → s'.cfg ∈ {c | Y ys c} → s'.tb = true ∧ s'.ib = β (s'.chkV P.b) := by
    intro s' hs' h1
    have h2 := wpP_mono _ (fun c' hc' => y_nil hY hc') (y_prog hY (gram_good P).nodup hp h1)
    rw [inss_append, wpP_append, wp_chain2 H.cs hreg₁ hreg₂ hs'] at h2
    obtain ⟨hl₂, hl₁, v₂, v₁, e2, e1, h3⟩ := h2
    simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_assertTB] at h3
    have hk : s'.chkV P.b < as₂.length := hl₂ ▸ ofB_lt _ _
    have hk1 : s'.chkV P.b < as₁.length := hl₁ ▸ ofB_lt _ _
    rw [run_cpy_mem hr₁ _ (List.getD_mem' hk1), rho_id] at e1
    obtain ⟨β', hβ'⟩ := run_bits_mem hr₂ _ (List.getD_mem' hk)
    rw [hβ', rho_bit] at e2
    refine ⟨?_, ?_⟩
    · rw [← e1]; exact h3.1
    · simp only [β, hβ']; exact e2.1
  have hpin : Pin P {c | Y ys c} (fun _ => true) β := fun s' hs' h1 => hpost s' hs' h1
  have hx := hsnd _ _ hpin
  have hall := ofB_all_true (g := fun _ => true) (n := 2 ^ P.b) (fun _ _ => rfl)
  refine ⟨ofB β (2 ^ P.b), by rw [H.hB]; exact ofB_lt _ _, ?_⟩
  rw [H.hB, show 2 ^ 2 ^ P.b - 1 = ofB (fun _ => true) (2 ^ P.b) by omega, hx, ← H.acc]
  exact ha

end Claims

end TOHard2

end FOND
