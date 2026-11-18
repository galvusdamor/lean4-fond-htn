import FondHtn.TOHard2.SoundK
/-!
# Completeness of the claims

**`FOND.TOHard2.complete`**: for all `t, i < 2 ^ D` the policy wins the claim `K (tabC t i)`
from every shaped state, with the postcondition `FOND.TOHard2.PinSet t i` (shaped states holding
the digits of `t` and `i` at the challenged index).  Induction on `t`; the digit types are the
actual carries (`inc_complete`, `dec_complete`, `cpy_complete`, `cmp_complete`).

**`FOND.TOHard2.root_complete`**: an accepting entry in the last row wins the root.
-/

set_option linter.unusedSimpArgs false

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

/-- The shaped states holding the digits of `t` and `i` at the challenged index. -/
def PinSet (P : Par) (t i : ℕ) : Set Cfg :=
  {c | ∃ s : St, Shaped s ∧ c = s.cfg ∧ s.tb = t.testBit (s.chkV P.b) ∧ s.ib = i.testBit (s.chkV P.b)}

section Aux

variable (P : Par)

theorem getI_mem_of_lt {α : Type} [Inhabited α] {l : List α} {j : ℕ} (hj : j < l.length) :
    l.getI j ∈ l := by
  rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _

theorem exists_getI_of_mem {α : Type} [Inhabited α] {l : List α} {x : α} (h : x ∈ l) :
    ∃ j < l.length, l.getI j = x := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨j, hj, by rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj]⟩

theorem chIn_mode {x : ℕ} (hx : x ∈ predCodes P) {m : ℕ} (hm : m < 3) :
    ChIn P (.inc true) (chN (modeI m) (KN x)) ∧ ChIn P (modeI m) (KN x) := by
  have hsub : modeChMeths P x ⊆ allChMeths P := by
    intro q hq
    simp only [allChMeths, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl ⟨x, hx, hq⟩)
  obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  · have e : modeI 0 = .inc false := rfl
    rw [e]
    refine ⟨chIn_of_sub P fun q hq => hsub ?_, chIn_of_sub P fun q hq => hsub ?_⟩ <;>
      simp only [modeChMeths, List.mem_append]
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hq))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hq))))
  · have e : modeI 1 = .cpy := rfl
    rw [e]
    refine ⟨chIn_of_sub P fun q hq => hsub ?_, chIn_of_sub P fun q hq => hsub ?_⟩ <;>
      simp only [modeChMeths, List.mem_append]
    · exact Or.inl (Or.inl (Or.inl (Or.inr hq)))
    · exact Or.inl (Or.inl (Or.inr hq))
  · have e : modeI 2 = .dec false := rfl
    rw [e]
    refine ⟨chIn_of_sub P fun q hq => hsub ?_, chIn_of_sub P fun q hq => hsub ?_⟩ <;>
      simp only [modeChMeths, List.mem_append]
    · exact Or.inl (Or.inr hq)
    · exact Or.inr hq

theorem chIn_true : ChIn P (.cmp 0 true) (chN (.cmp 1 false) bbN) ∧ ChIn P (.cmp 1 false) bbN := by
  constructor <;> refine chIn_of_sub P fun q hq => ?_ <;>
    simp only [allChMeths, List.mem_append] <;> simp_all

theorem chIn_none : ChIn P (.cmp 1 true) (chN .cpy bbN) ∧ ChIn P .cpy bbN := by
  constructor <;> refine chIn_of_sub P fun q hq => ?_ <;>
    simp only [allChMeths, List.mem_append] <;> simp_all

theorem chIn_root {a : ℕ} (ha : a ∈ P.acc) :
    ChIn P .cpy (chN .bits (KN a)) ∧ ChIn P .bits (KN a) := by
  constructor <;> refine chIn_of_sub P fun q hq => ?_ <;>
    simp only [allChMeths, List.mem_append, List.mem_flatMap] <;>
    exact Or.inr ⟨a, ha, by simp [hq]⟩

theorem mid_pred {j : ℕ} (hj : j < P.mid.length) :
    (P.mid.getI j).2.1 ∈ predCodes P ∧ (P.mid.getI j).2.2.1 ∈ predCodes P ∧
      (P.mid.getI j).2.2.2 ∈ predCodes P := by
  have h := getI_mem_of_lt hj
  refine ⟨?_, ?_, ?_⟩ <;> simp only [predCodes, List.mem_append, List.mem_flatMap] <;>
    exact Or.inl (Or.inl ⟨_, h, by simp⟩)

theorem lft_pred {j : ℕ} (hj : j < P.lft.length) :
    (P.lft.getI j).2.1 ∈ predCodes P ∧ (P.lft.getI j).2.2 ∈ predCodes P := by
  have h := getI_mem_of_lt hj
  refine ⟨?_, ?_⟩ <;> simp only [predCodes, List.mem_append, List.mem_flatMap] <;>
    exact Or.inl (Or.inr ⟨_, h, by simp⟩)

theorem rgt_pred {j : ℕ} (hj : j < P.rgt.length) :
    (P.rgt.getI j).2.1 ∈ predCodes P ∧ (P.rgt.getI j).2.2 ∈ predCodes P := by
  have h := getI_mem_of_lt hj
  refine ⟨?_, ?_⟩ <;> simp only [predCodes, List.mem_append, List.mem_flatMap] <;>
    exact Or.inr ⟨_, h, by simp⟩

/-! ### Runs for given numbers -/

theorem rel_testBit {cs : List (List ℕ)} {as : List AT} {z o : ℕ → Bool} {n x : ℕ}
    (hl : as.length = n) (h : Rel cs as z o) (ho : ofB o n = x) (hx : x < 2 ^ n) :
    Rel cs as z x.testBit :=
  rel_congr h fun d hd => (ofB_eq_iff hx).1 ho d (hl ▸ hd)

theorem run_time {cs : List (List ℕ)} {t : ℕ} (ht : t + 1 < 2 ^ 2 ^ P.b) :
    ∃ asT, asT.length = 2 ^ P.b ∧ Run (Comp.inc true).aut asT (Comp.inc true).aut.acc ∧
      Rel cs asT t.testBit (t + 1).testBit := by
  have htz : ofB t.testBit (2 ^ P.b) = t := ofB_testBit (by omega)
  obtain ⟨as, hl, hr, o, ho, hv⟩ := inc_complete (cs := cs) true (z := t.testBit)
    (Nat.one_le_two_pow) (by rw [htz]; exact ht)
  exact ⟨as, hl, hr, rel_testBit hl ho (by rw [hv, htz]) ht⟩

theorem run_cell {cs : List (List ℕ)} {m i' i : ℕ} (hm : m < 3) (hi' : i' < 2 ^ 2 ^ P.b)
    (hi : i < 2 ^ 2 ^ P.b) (hrel : (m = 0 → i = i' + 1) ∧ (m = 1 → i = i') ∧ (m = 2 → i' = i + 1)) :
    ∃ asI, asI.length = 2 ^ P.b ∧ Run (modeI m).aut asI (modeI m).aut.acc ∧
      Rel cs asI i'.testBit i.testBit := by
  have hz : ofB i'.testBit (2 ^ P.b) = i' := ofB_testBit hi'
  interval_cases m
  · obtain ⟨as, hl, hr, o, ho, hv⟩ := inc_complete (cs := cs) false (z := i'.testBit)
      (Nat.one_le_two_pow) (by rw [hz]; have := hrel.1 rfl; omega)
    exact ⟨as, hl, hr, rel_testBit hl ho (by rw [hv, hz, hrel.1 rfl]) hi⟩
  · obtain ⟨as, hl, hr, ho⟩ := cpy_complete (cs := cs) i'.testBit (2 ^ P.b) Nat.one_le_two_pow
    rw [hrel.2.1 rfl]
    exact ⟨as, hl, hr, ho⟩
  · obtain ⟨as, hl, hr, o, ho, hv⟩ := dec_complete (cs := cs) false (z := i'.testBit)
      (Nat.one_le_two_pow) (by rw [hz, hrel.2.2 rfl]; omega)
    exact ⟨as, hl, hr, rel_testBit hl ho (by rw [hz, hrel.2.2 rfl] at hv; omega) hi⟩

end Aux

section Complete

variable {P : Par} {d : TabData} {tabC : ℕ → ℕ → ℕ} (H : Hyp P d tabC)
include H

/-- The chains carry pinned states to pinned states. -/
theorem pin_transfer {asT asI : List AT} (hregT : ∀ a ∈ asT, a = .id ∨ a.reg = true)
    (hregI : ∀ a ∈ asI, a = .id ∨ a.reg = false) (hlT : asT.length = 2 ^ P.b)
    (hlI : asI.length = 2 ^ P.b) {t' i' t i : ℕ} (hRT : Rel P.cs asT t'.testBit t.testBit)
    (hRI : Rel P.cs asI i'.testBit i.testBit) :
    PinSet P t' i' ⊆ wpP (inss (chain P.b P.cs asI ++ chain P.b P.cs asT)) (PinSet P t i) := by
  rintro c ⟨s, hs, rfl, htb, hib⟩
  rw [wp_chain2 H.cs hregT hregI hs]
  have hk : s.chkV P.b < 2 ^ P.b := ofB_lt _ _
  refine ⟨hlI, hlT, i.testBit (s.chkV P.b), t.testBit (s.chkV P.b), ?_, ?_,
    ⟨_, shaped_fn _, rfl, rfl, rfl⟩⟩
  · rw [hib]; exact hRI _ (hlI ▸ hk)
  · rw [htb]; exact hRT _ (hlT ▸ hk)

/-- **A challenge body**, completeness. -/
theorem mode_complete {m x : ℕ} (hm3 : m < 3) (hx : x ∈ predCodes P)
    {postP : List (ℕ × List ASpec)} (hpost : ∀ q ∈ postP, q ∈ (gram P).insL) {s : St}
    (hv : s.val (4 + m) = true) {asT asI : List AT} (hT : Run (Comp.inc true).aut asT (Comp.inc true).aut.acc)
    (hI : Run (modeI m).aut asI (modeI m).aut.acc) {Ψ Ψ' : Set Cfg}
    (hin : LG (gram P) [(true, KN x)] s.cfg Ψ')
    (hsub : Ψ' ⊆ wpP (inss (chain P.b P.cs asI ++ chain P.b P.cs asT ++ postP)) Ψ) :
    LG (gram P) (modeBody m x ++ syms postP) s.cfg Ψ := by
  obtain ⟨hc₁, hc₂⟩ := chIn_mode P hx hm3
  rw [modeBody_eq, List.cons_append]
  have hmI : assertMI m ∈ (gram P).insL := by
    apply insRaw_mem_of_mem; interval_cases m <;> simp
  refine LG.ins hmI ((wp_assertM).2 ⟨hv, ?_⟩)
  show LG (gram P) ((true, chN (.inc true) (chN (modeI m) (KN x))) :: syms postP) s.cfg Ψ
  refine LG.ch2 P hc₁ hc₂ hT hI ?_
  rw [List.cons_append, ← List.singleton_append, ← syms_append]
  refine LG.append' (hin.mono fun c hc => ?_)
  show LG (gram P) (syms (chain P.b P.cs asI ++ chain P.b P.cs asT ++ postP)) c Ψ
  rw [← List.append_nil (syms _)]
  refine LG.prog (fun q hq => ?_) ?_
  · simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact chain_mem P (run_ok (modeI_ok P H.two_le m) hI) q hq
    · exact chain_mem P (run_ok (A := .inc true) trivial hT) q hq
    · exact hpost q hq
  · exact wpP_mono _ (fun c' hc' => LG.nil hc') (hsub hc)

/-! ## The first row -/

theorem kMeths_mem {q : ℕ × List (Bool × ℕ)} (h : q ∈ kMeths P) : q ∈ (gram P).methL :=
  mem_K_of_mem_kMeths P h

/-- **A prefix cell.** -/
theorem complete_pref {i : ℕ} (hi : i < P.baseU.length) {s : St} (hs : Shaped s) :
    LG (gram P) [(true, KN (P.baseU.getI i))] s.cfg (PinSet P 0 i) := by
  have hok : (AT.ce (2 + i)).Ok P.cs.length := by show 2 + i < P.cs.length; rw [H.csl]; omega
  have hmeth : (KN (P.baseU.getI i), prefBody P i) ∈ (gram P).methL := kMeths_mem H (by
    simp only [kMeths, List.mem_append, List.mem_map, List.mem_range, List.mem_cons]
    exact Or.inl (Or.inr ⟨i, hi, rfl⟩))
  have hp : ∀ q ∈ pickChks P ++ [clrTBI, guessIBI, setEQ] ++ actP P.b P.cs (.ce (2 + i)),
      q ∈ (gram P).insL := by
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact pickChks_mem P q hq
    · exact insRaw_mem_of_mem P (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                                    rcases hq with rfl | rfl | rfl <;> simp)
    · exact actP_mem P hok q hq
  have hiD : i < 2 ^ 2 ^ P.b := by
    have := H.good.hc₂; have := H.good.hc₁₂; rw [H.c₁, H.hB] at *; omega
  refine LG.comp hmeth ?_
  rw [prefBody]
  refine LG.prog hp ?_
  rw [inss_append, inss_append, wpP_append, wpP_append, wp_pickChks]
  intro g
  simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_clrTB, wp_guessIB, wp_setEQ]
  refine ⟨kDig P.cs (2 + i) (ofB g P.b), hs.1, ?_⟩
  rw [wp_act H.cs]
  simp only [if_true, AT.reg, St.reg, St.setReg, Bool.false_eq_true, if_false, rho_ce]
  refine ⟨_, ⟨?_, rfl⟩, LG.nil ⟨_, ?_, rfl, ?_, ?_⟩⟩
  · have e : ofB (fun r => if r < P.b then g r else s.chk r) P.b = ofB g P.b :=
      ofB_congr (fun r hr => by simp [hr])
    simp only [St.chkV, kDig, e]
  · exact hs
  · simp
  · show kDig P.cs (2 + i) (ofB g P.b) = i.testBit (ofB (fun r => if r < P.b then g r else s.chk r) P.b)
    rw [show ofB (fun r => if r < P.b then g r else s.chk r) P.b = ofB g P.b from
      ofB_congr (fun r hr => by simp [hr])]
    exact (ofB_eq_iff hiD).1 (H.kc i hi) _ (ofB_lt _ _)

omit H in
theorem Comp.reg_of_check' {A : Comp} (hA : A.Check) : A.reg = false := Comp.reg_of_check hA

/-- **Two check chains after `BB`.** -/
theorem complete_bb {A₁ A₂ : Comp} (hA₁ : A₁.Check) (hA₂ : A₂.Check) (hok₁ : A₁.Ok P.cs.length)
    (hok₂ : A₂.Ok P.cs.length) (hc₁ : ChIn P A₁ (chN A₂ bbN)) (hc₂ : ChIn P A₂ bbN) {as₁ as₂ : List AT}
    (hr₁ : Run A₁.aut as₁ A₁.aut.acc) (hr₂ : Run A₂.aut as₂ A₂.aut.acc) (hl₁ : as₁.length = 2 ^ P.b)
    (hl₂ : as₂.length = 2 ^ P.b) {i : ℕ} (hR₁ : Rel P.cs as₁ i.testBit i.testBit)
    (hR₂ : Rel P.cs as₂ i.testBit i.testBit) {s : St} (hs : Shaped s) :
    LG (gram P) [(true, chN A₁ (chN A₂ bbN))] s.cfg (PinSet P 0 i) := by
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
  have hreg₁ : ∀ a ∈ as₁, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hr₁ a ha with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (Comp.reg_of_check' hA₁))
  have hreg₂ : ∀ a ∈ as₂, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hr₂ a ha with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (Comp.reg_of_check' hA₂))
  refine LG.ch2 P hc₁ hc₂ hr₁ hr₂ ?_
  refine LG.comp (mem_bb P) ?_
  have e : bbBody P ++ (syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++ []) =
      syms (pickChks P ++ [clrTBI, guessIBI] ++ chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++ [] := by
    simp [bbBody, List.append_assoc]
  rw [show (syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁)).append [] =
    syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++ [] from rfl, e]
  refine LG.prog hp ?_
  rw [inss_append, inss_append, inss_append, wpP_append, wpP_append, wpP_append, wp_pickChks]
  intro g
  simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_clrTB, wp_guessIB]
  set k := ofB g P.b with hk
  refine ⟨i.testBit k, ?_⟩
  rw [← wpP_append, ← inss_append]
  let st : St := { s with chk := (fun r => if r < P.b then g r else s.chk r), tb := false, ib := i.testBit k }
  have hck : st.chkV P.b = k := chkV_pick P _ g
  have hsh : Shaped st := hs
  refine (wp_chain2I H.cs hreg₁ hreg₂ hsh).2 ⟨hl₂, hl₁, i.testBit k, i.testBit k,
      ?_, ?_, LG.nil ⟨_, shaped_fn _, rfl, ?_, ?_⟩⟩
  · rw [hck]; exact hR₂ k (hl₂ ▸ ofB_lt _ _)
  · rw [hck]; exact hR₁ k (hl₁ ▸ ofB_lt _ _)
  · show false = (0 : ℕ).testBit _; simp
  · show i.testBit k = i.testBit (ofB (fun r => if r < P.b then g r else s.chk r) P.b)
    rw [← hck]; rfl

/-- **The cells holding `1`.** -/
theorem complete_true {i : ℕ} (h₁ : d.c₁ ≤ i) (h₂ : i < d.c₂) {s : St} (hs : Shaped s) :
    LG (gram P) [(true, KN P.codeTrue)] s.cfg (PinSet P 0 i) := by
  have h2 := H.two_le
  have hiD : i < 2 ^ 2 ^ P.b := by have := H.good.hc₂; rw [H.hB] at this; omega
  have hz : ofB i.testBit (2 ^ P.b) = i := ofB_testBit hiD
  obtain ⟨as₁, hl₁, hr₁, hR₁⟩ := cmp_complete (cs := P.cs) 0 true (z := i.testBit) (n := 2 ^ P.b)
    Nat.one_le_two_pow (by rw [hz, H.k0]; simp [h₁])
  obtain ⟨as₂, hl₂, hr₂, hR₂⟩ := cmp_complete (cs := P.cs) 1 false (z := i.testBit) (n := 2 ^ P.b)
    Nat.one_le_two_pow (by rw [hz, H.k1]; simp; omega)
  have hmeth : (KN P.codeTrue, [(true, chN (.cmp 0 true) (chN (.cmp 1 false) bbN))]) ∈
      (gram P).methL := kMeths_mem H (by simp [kMeths])
  refine LG.comp hmeth ?_
  exact complete_bb H (A₁ := .cmp 0 true) (A₂ := .cmp 1 false) trivial trivial
    (show 0 < P.cs.length by omega) (show 1 < P.cs.length by omega) (chIn_true P).1 (chIn_true P).2
    hr₁ hr₂ hl₁ hl₂ hR₁ hR₂ hs

/-- **The blank cells.** -/
theorem complete_none {i : ℕ} (h₂ : d.c₂ ≤ i) (hi : i < 2 ^ 2 ^ P.b) {s : St} (hs : Shaped s) :
    LG (gram P) [(true, KN P.codeNone)] s.cfg (PinSet P 0 i) := by
  have h2 := H.two_le
  have hz : ofB i.testBit (2 ^ P.b) = i := ofB_testBit hi
  obtain ⟨as₁, hl₁, hr₁, hR₁⟩ := cmp_complete (cs := P.cs) 1 true (z := i.testBit) (n := 2 ^ P.b)
    Nat.one_le_two_pow (by rw [hz, H.k1]; simp [h₂])
  obtain ⟨as₂, hl₂, hr₂, hR₂⟩ := cpy_complete (cs := P.cs) i.testBit (2 ^ P.b) Nat.one_le_two_pow
  have hmeth : (KN P.codeNone, [(true, chN (.cmp 1 true) (chN .cpy bbN))]) ∈
      (gram P).methL := kMeths_mem H (by simp [kMeths])
  refine LG.comp hmeth ?_
  exact complete_bb H (A₁ := .cmp 1 true) (A₂ := .cpy) trivial trivial
    (show 1 < P.cs.length by omega) trivial (chIn_none P).1 (chIn_none P).2
    hr₁ hr₂ hl₁ hl₂ hR₁ hR₂ hs

/-! ## The steps -/

/-- The induction hypothesis of completeness (for time `t`). -/
def IHc (P : Par) (tabC : ℕ → ℕ → ℕ) (t : ℕ) : Prop :=
  ∀ i < 2 ^ 2 ^ P.b, ∀ s : St, Shaped s → LG (gram P) [(true, KN (tabC t i))] s.cfg (PinSet P t i)

/-- **A challenge**, from the predecessor claim. -/
theorem mode_finish {t : ℕ} (ih : IHc P tabC t) (ht : t + 1 < 2 ^ 2 ^ P.b) {m i' i : ℕ} (hm : m < 3)
    (hi' : i' < 2 ^ 2 ^ P.b) (hi : i < 2 ^ 2 ^ P.b)
    (hrel : (m = 0 → i = i' + 1) ∧ (m = 1 → i = i') ∧ (m = 2 → i' = i + 1))
    (hx : tabC t i' ∈ predCodes P) {postP : List (ℕ × List ASpec)}
    (hpost : ∀ q ∈ postP, q ∈ (gram P).insL) {Ψ : Set Cfg}
    (hpS : PinSet P (t + 1) i ⊆ wpP (inss postP) Ψ) {s : St} (hs : Shaped s)
    (hv : s.val (4 + m) = true) :
    LG (gram P) (modeBody m (tabC t i') ++ syms postP) s.cfg Ψ := by
  obtain ⟨asT, hlT, hT, hRT⟩ := run_time P (cs := P.cs) ht
  obtain ⟨asI, hlI, hI, hRI⟩ := run_cell P (cs := P.cs) hm hi' hi hrel
  have hregI : ∀ a ∈ asI, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hI a ha with h | h
    · exact Or.inl h
    · right; rw [h]; unfold modeI; split_ifs <;> rfl
  refine mode_complete H hm hx hpost hv hT hI (ih i' hi' s hs) fun c hc => ?_
  have := pin_transfer H (run_reg hT) hregI hlT hlI hRT hRI hc
  rw [inss_append, wpP_append]
  exact wpP_mono _ hpS this

omit H in
theorem pin_assertIB {t i : ℕ} {β : Bool} (hβ : ∀ k < 2 ^ P.b, i.testBit k = β) :
    PinSet P t i ⊆ wpP (inss [assertIBI β]) (PinSet P t i) := by
  rintro c ⟨s, hs, rfl, htb, hib⟩
  simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_assertIB]
  exact ⟨by rw [hib]; exact hβ _ (ofB_lt _ _), ⟨s, hs, rfl, htb, hib⟩⟩

theorem subMeths_mem {q : ℕ × List (Bool × ℕ)} (h : q ∈ subMeths P) : q ∈ (gram P).methL :=
  mem_sub_of_mem P h

/-- **The middle rule.** -/
theorem complete_mid {t i : ℕ} (ih : IHc P tabC t) (ht : t + 1 < 2 ^ 2 ^ P.b) (hi0 : 0 < i)
    (hi : i + 1 < 2 ^ 2 ^ P.b) {s : St} (hs : Shaped s) :
    LG (gram P) [(true, KN (tabC (t + 1) i))] s.cfg (PinSet P (t + 1) i) := by
  have hB := H.hB
  have hq := H.good.mid_c t i hi0 (by rw [hB]; exact hi) (by rw [hB]; exact ht)
  rw [← H.mid] at hq
  obtain ⟨j, hj, hjq⟩ := exists_getI_of_mem hq
  obtain ⟨hx1, hx2, hx3⟩ := mid_pred P hj
  rw [hjq] at hx1 hx2 hx3
  have hK : (KN (tabC (t + 1) i), [(false, pick3I.1), (true, subN 0 j)]) ∈ (gram P).methL :=
    kMeths_mem H (by
      simp only [kMeths, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨j, hj, by rw [hjq]⟩))))
  have hsub : ∀ m < 3, (subN 0 j, modeBody m (if m = 0 then tabC t (i - 1) else if m = 1 then tabC t i
      else tabC t (i + 1))) ∈ (gram P).methL := by
    intro m hm
    apply subMeths_mem H
    simp only [subMeths, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false]
    refine Or.inl (Or.inl ⟨j, hj, ?_⟩)
    rw [hjq]
    interval_cases m <;> simp
  refine LG.comp hK ?_
  have hpick : pick3I ∈ (gram P).insL := insRaw_mem_of_mem P (by simp)
  refine LG.ins hpick (wp_pick3.2 ⟨?_, ?_, ?_⟩) <;> show LG _ [(true, subN 0 j)] _ _
  · refine LG.comp (hsub 0 (by norm_num)) ?_
    simpa using mode_finish H ih ht (m := 0) (i' := i - 1) (by norm_num) (by omega) (by omega)
      ⟨fun _ => by omega, by simp, by simp⟩ hx1 (postP := []) (by simp) (fun c hc => hc) (shaped_modeSt hs _ _ _) rfl
  · refine LG.comp (hsub 1 (by norm_num)) ?_
    simpa using mode_finish H ih ht (m := 1) (i' := i) (by norm_num) (by omega) (by omega)
      ⟨by simp, fun _ => rfl, by simp⟩ hx2 (postP := []) (by simp) (fun c hc => hc) (shaped_modeSt hs _ _ _) rfl
  · refine LG.comp (hsub 2 (by norm_num)) ?_
    simpa using mode_finish H ih ht (m := 2) (i' := i + 1) (by norm_num) (by omega) (by omega)
      ⟨by simp, by simp, fun _ => rfl⟩ hx3 (postP := []) (by simp) (fun c hc => hc) (shaped_modeSt hs _ _ _) rfl

/-- **Cell `0`.** -/
theorem complete_lft {t : ℕ} (ih : IHc P tabC t) (ht : t + 1 < 2 ^ 2 ^ P.b) {s : St} (hs : Shaped s) :
    LG (gram P) [(true, KN (tabC (t + 1) 0))] s.cfg (PinSet P (t + 1) 0) := by
  have hB := H.hB
  have h2 : 2 ≤ 2 ^ 2 ^ P.b := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ 2 ^ P.b := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have hq := H.good.lft_c t (by rw [hB]; exact ht)
  rw [← H.lft] at hq
  obtain ⟨j, hj, hjq⟩ := exists_getI_of_mem hq
  obtain ⟨hx1, hx2⟩ := lft_pred P hj
  rw [hjq] at hx1 hx2
  have hK : (KN (tabC (t + 1) 0), [(false, pickCRI.1), (true, subN 1 j)]) ∈ (gram P).methL :=
    kMeths_mem H (by
      simp only [kMeths, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, by rw [hjq]⟩))))
  have hsub : ∀ m, (m = 1 ∨ m = 2) → (subN 1 j, modeBody m (if m = 1 then tabC t 0 else tabC t 1) ++
      [(false, (assertIBI false).1)]) ∈ (gram P).methL := by
    intro m hm
    apply subMeths_mem H
    simp only [subMeths, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false]
    refine Or.inl (Or.inr ⟨j, hj, ?_⟩)
    rw [hjq]
    rcases hm with rfl | rfl <;> simp
  have hpost : ∀ q ∈ [assertIBI false], q ∈ (gram P).insL := by
    intro q hq; exact insRaw_mem_of_mem P (by simp at hq; subst hq; simp)
  have hpS := pin_assertIB (P := P) (t := t + 1) (i := 0) (β := false) (fun k _ => Nat.zero_testBit k)
  refine LG.comp hK ?_
  have hpick : pickCRI ∈ (gram P).insL := insRaw_mem_of_mem P (by simp)
  refine LG.ins hpick (wp_pickCR.2 ⟨?_, ?_⟩) <;> show LG _ [(true, subN 1 j)] _ _
  · refine LG.comp (hsub 1 (Or.inl rfl)) ?_
    simpa using mode_finish H ih ht (m := 1) (i' := 0) (by norm_num) (by omega) (by omega)
      ⟨by simp, fun _ => rfl, by simp⟩ hx1 hpost hpS (shaped_modeSt hs _ _ _) rfl
  · refine LG.comp (hsub 2 (Or.inr rfl)) ?_
    simpa using mode_finish H ih ht (m := 2) (i' := 1) (by norm_num) (by omega) (by omega)
      ⟨by simp, by simp, fun _ => rfl⟩ hx2 hpost hpS (shaped_modeSt hs _ _ _) rfl

/-- **The last cell.** -/
theorem complete_rgt {t : ℕ} (ih : IHc P tabC t) (ht : t + 1 < 2 ^ 2 ^ P.b) {s : St} (hs : Shaped s) :
    LG (gram P) [(true, KN (tabC (t + 1) d.mx))] s.cfg (PinSet P (t + 1) d.mx) := by
  have hB := H.hB
  have hmx := H.good.hmx
  rw [hB] at hmx
  have h2 : 2 ≤ 2 ^ 2 ^ P.b := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ 2 ^ P.b := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have hq := H.good.rgt_c t (by rw [hB]; exact ht)
  rw [← H.rgt] at hq
  obtain ⟨j, hj, hjq⟩ := exists_getI_of_mem hq
  obtain ⟨hx1, hx2⟩ := rgt_pred P hj
  rw [hjq] at hx1 hx2
  have hK : (KN (tabC (t + 1) d.mx), [(false, pickLCI.1), (true, subN 2 j)]) ∈ (gram P).methL :=
    kMeths_mem H (by
      simp only [kMeths, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inr ⟨j, hj, by rw [hjq]⟩)))
  have hsub : ∀ m, (m = 0 ∨ m = 1) → (subN 2 j, modeBody m (if m = 0 then tabC t (d.mx - 1)
      else tabC t d.mx) ++ [(false, (assertIBI true).1)]) ∈ (gram P).methL := by
    intro m hm
    apply subMeths_mem H
    simp only [subMeths, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false]
    refine Or.inr ⟨j, hj, ?_⟩
    rw [hjq]
    rcases hm with rfl | rfl <;> simp
  have hpost : ∀ q ∈ [assertIBI true], q ∈ (gram P).insL := by
    intro q hq; exact insRaw_mem_of_mem P (by simp at hq; subst hq; simp)
  have hpS := pin_assertIB (P := P) (t := t + 1) (i := d.mx) (β := true)
    (fun k hk => by rw [hmx, Nat.testBit_two_pow_sub_one]; simpa using hk)
  refine LG.comp hK ?_
  have hpick : pickLCI ∈ (gram P).insL := insRaw_mem_of_mem P (by simp)
  refine LG.ins hpick (wp_pickLC.2 ⟨?_, ?_⟩) <;> show LG _ [(true, subN 2 j)] _ _
  · refine LG.comp (hsub 0 (Or.inl rfl)) ?_
    simpa using mode_finish H ih ht (m := 0) (i' := d.mx - 1) (by norm_num) (by omega) (by omega)
      ⟨fun _ => by omega, by simp, by simp⟩ hx1 hpost hpS (shaped_modeSt hs _ _ _) rfl
  · refine LG.comp (hsub 1 (Or.inr rfl)) ?_
    simpa using mode_finish H ih ht (m := 1) (i' := d.mx) (by norm_num) (by omega) (by omega)
      ⟨by simp, fun _ => rfl, by simp⟩ hx2 hpost hpS (shaped_modeSt hs _ _ _) rfl

/-! ## Completeness of the claims and of the root -/

/-- **Completeness of the claims.** -/
theorem complete : ∀ t, t < 2 ^ 2 ^ P.b → IHc P tabC t := by
  have hB := H.hB
  intro t
  induction t with
  | zero =>
    intro _ i hi s hs
    by_cases h1 : i < P.baseU.length
    · rw [H.good.base i (by rw [H.c₁]; exact h1), ← H.baseU]
      exact complete_pref H h1 hs
    · by_cases h2 : i < d.c₂
      · rw [H.good.tru i (by rw [H.c₁]; omega) h2, ← H.codeTrue]
        exact complete_true H (by rw [H.c₁]; omega) h2 hs
      · rw [H.good.non i (by omega) (by rw [hB]; exact hi), ← H.codeNone]
        exact complete_none H (by omega) hi hs
  | succ t ih =>
    intro ht i hi s hs
    have ih' := ih (by omega)
    have hmx := H.good.hmx
    rw [hB] at hmx
    by_cases h0 : i = 0
    · subst h0; exact complete_lft H ih' ht hs
    · by_cases h1 : i = d.mx
      · subst h1; exact complete_rgt H ih' ht hs
      · exact complete_mid H ih' ht (by omega) (by omega) hs

/-- **Completeness of the root.** -/
theorem root_complete (h : ∃ i < 2 ^ d.B, tabC (2 ^ d.B - 1) i ∈ d.acc) :
    LG (gram P) [(true, rootN)] s₀.cfg Set.univ := by
  obtain ⟨i, hi, ha⟩ := h
  rw [H.hB] at hi ha
  rw [← H.acc] at ha
  set a := tabC (2 ^ 2 ^ P.b - 1) i with hadef
  obtain ⟨as₁, hl₁, hr₁, -⟩ := cpy_complete (cs := P.cs) (fun _ => true) (2 ^ P.b) Nat.one_le_two_pow
  set as₂ : List AT := (List.range (2 ^ P.b)).map fun k => .bit (i.testBit k) with has₂
  have hr₂ : Run Comp.bits.aut as₂ Comp.bits.aut.acc := exists_run_bits _ _ Nat.one_le_two_pow
  have hl₂ : as₂.length = 2 ^ P.b := by simp [has₂]
  have hreg₁ : ∀ a ∈ as₁, a = .id ∨ a.reg = true := fun a ha => Or.inl (run_cpy_mem hr₁ a ha)
  have hreg₂ : ∀ a ∈ as₂, a = .id ∨ a.reg = false := fun a ha => by
    rcases run_reg hr₂ a ha with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hp : ∀ q ∈ chain P.b P.cs as₂ ++ chain P.b P.cs as₁ ++ [assertTBI], q ∈ (gram P).insL := by
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | hq) | rfl
    · exact chain_mem P (run_ok (A := .bits) trivial hr₂) q hq
    · exact chain_mem P (run_ok (A := .cpy) trivial hr₁) q hq
    · exact insRaw_mem_of_mem P (by simp)
  refine LG.comp (mem_root P ha) ?_
  refine LG.ch2 P (chIn_root P ha).1 (chIn_root P ha).2 hr₁ hr₂ ?_
  have e : (true, KN a) :: syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁) ++
      ([(false, assertTBI.1)].append []) =
      [(true, KN a)] ++ (syms (chain P.b P.cs as₂ ++ chain P.b P.cs as₁ ++ [assertTBI]) ++ []) := by
    simp
  rw [e]
  refine LG.append' ((complete H _ (by omega) i hi s₀ shaped_s₀).mono fun c hc => ?_)
  obtain ⟨st, hst, rfl, htb, hib⟩ := hc
  refine LG.prog hp ?_
  rw [inss_append, wpP_append, wp_chain2 H.cs hreg₁ hreg₂ hst]
  have hk : st.chkV P.b < 2 ^ P.b := ofB_lt _ _
  have hgd : as₂.getD (st.chkV P.b) .id = .bit (i.testBit (st.chkV P.b)) := by
    rw [List.getD_eq_getElem _ _ (hl₂ ▸ hk)]; simp [has₂]
  refine ⟨hl₂, hl₁, st.ib, st.tb, ?_, ?_, ?_⟩
  · rw [hgd, rho_bit]; exact ⟨hib, rfl⟩
  · rw [run_cpy_mem hr₁ _ (List.getD_mem' (hl₁ ▸ hk)), rho_id]
  · simp only [inss_cons, inss_nil, wpP_cons, wpP_nil, wp_assertTB]
    refine ⟨?_, LG.nil trivial⟩
    show st.tb = true
    rw [htb, Nat.testBit_two_pow_sub_one]; simpa using hk

end Complete

end TOHard2

end FOND
