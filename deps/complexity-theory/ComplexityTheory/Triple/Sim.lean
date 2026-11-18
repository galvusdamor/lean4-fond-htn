import ComplexityTheory.Triple.Zero
/-!
# Triples replace zero tests (CJLLO Lemma 7, for any number of counters)

A counter machine with zero tests (`KTr`, `KStep`, `KReach trs n`: runs with exactly `n` zero
tests) over the counters `cs` is compiled into a counter system without zero tests (`IsR`): the
simulated counters `sim y`, the triple `a`, `b`, `c` and the temporaries `t`, `u _`.  An
increment moves a unit from `a` to the counter, a decrement back; a zero test of `x` (the
transition number `i`) runs the gadget `Zero(x)` of `Zero.lean` at the control states `g i _ _`
and then decrements `b`.

* **`sim_sound`**: a run of the compiled system from a triple `triple A B` to a final configuration
  (`b = c = 0`, simulated counters `0`) projects to a run of the machine with exactly `B` zero
  tests.  Proof: `phi_of_reach`, a backward induction whose invariant inside a gadget is "the rest
  of the gadget, then the goal at its exit" (`Rest`); the invariant `Holds` / `Broken` of
  `Arith.lean` shows that every completed test was honest.
* **`sim_complete`**: conversely, a run with exactly `B` zero tests and `L` steps is simulated
  from `triple L B` (`sim_run`, `gadget_pass`).
-/

namespace HTN

namespace Triple

/-- Counter operations, with zero tests. -/
inductive KOp (ι : Type) where
  | nop : KOp ι
  | inc (x : ι) : KOp ι
  | dec (x : ι) : KOp ι
  | zero (x : ι) : KOp ι

/-- A transition of a counter machine with zero tests. -/
structure KTr (Q ι : Type) where
  src : Q
  op : KOp ι
  dst : Q

variable {Q ι : Type} [DecidableEq ι]

/-- **A step**, with its number of zero tests. -/
inductive KStep (trs : List (KTr Q ι)) : ℕ → Q × (ι → ℕ) → Q × (ι → ℕ) → Prop
  | nop (t : KTr Q ι) (ht : t ∈ trs) (h : t.op = .nop) (v : ι → ℕ) :
      KStep trs 0 (t.src, v) (t.dst, v)
  | inc (t : KTr Q ι) (ht : t ∈ trs) (x : ι) (h : t.op = .inc x) (v : ι → ℕ) :
      KStep trs 0 (t.src, v) (t.dst, Function.update v x (v x + 1))
  | dec (t : KTr Q ι) (ht : t ∈ trs) (x : ι) (h : t.op = .dec x) (v : ι → ℕ) (hv : 1 ≤ v x) :
      KStep trs 0 (t.src, v) (t.dst, Function.update v x (v x - 1))
  | zero (t : KTr Q ι) (ht : t ∈ trs) (x : ι) (h : t.op = .zero x) (v : ι → ℕ) (hv : v x = 0) :
      KStep trs 1 (t.src, v) (t.dst, v)

/-- **Runs with exactly `n` zero tests.** -/
inductive KReach (trs : List (KTr Q ι)) : ℕ → Q × (ι → ℕ) → Q × (ι → ℕ) → Prop
  | refl (x : Q × (ι → ℕ)) : KReach trs 0 x x
  | head {m n : ℕ} {x y z : Q × (ι → ℕ)} : KStep trs m x y → KReach trs n y z →
      KReach trs (m + n) x z

/-! ### The compiled system -/

/-- The counters of the compiled system. -/
inductive Ct (ι : Type) where
  | sim (y : ι) : Ct ι
  | a : Ct ι
  | b : Ct ι
  | c : Ct ι
  | t : Ct ι
  | u (o : Option ι) : Ct ι
  deriving DecidableEq

/-- The temporaries. -/
def uMap : Ct ι → Ct ι
  | .a => .u none
  | .sim y => .u (some y)
  | _ => .t

/-- The gadget testing `x`. -/
def zd (cs : List ι) (x : ι) : ZD (Ct ι) :=
  ⟨.a, .t, .sim x, .c, .b, (cs.erase x).map .sim, uMap⟩

/-- The control states: the machine's, and the states `g i ph j` of the gadget of the transition
number `i` (phase `ph`, loop `j`). -/
inductive CL (Q : Type) where
  | main (q : Q) : CL Q
  | g (i : ℕ) (ph : Bool) (j : ℕ) : CL Q

/-- **The rules of the compiled system.** -/
inductive IsR (trs : List (KTr Q ι)) (cs : List ι) : Rule (CL Q) (Ct ι) → Prop
  | nop (t : KTr Q ι) (ht : t ∈ trs) (h : t.op = .nop) :
      IsR trs cs ⟨.main t.src, 0, 0, .main t.dst⟩
  | inc (t : KTr Q ι) (ht : t ∈ trs) (x : ι) (h : t.op = .inc x) :
      IsR trs cs ⟨.main t.src, Pi.single .a 1, Pi.single (.sim x) 1, .main t.dst⟩
  | dec (t : KTr Q ι) (ht : t ∈ trs) (x : ι) (h : t.op = .dec x) :
      IsR trs cs ⟨.main t.src, Pi.single (.sim x) 1, Pi.single .a 1, .main t.dst⟩
  | enter (i : ℕ) (t : KTr Q ι) (hi : trs[i]? = some t) (x : ι) (h : t.op = .zero x) :
      IsR trs cs ⟨.main t.src, 0, 0, .g i false 0⟩
  | loop (i : ℕ) (t : KTr Q ι) (hi : trs[i]? = some t) (x : ι) (h : t.op = .zero x) (ph : Bool)
      (j : ℕ) (s d e : Ct ι)
      (hj : (if ph then (zd cs x).l2 else (zd cs x).l1)[j]? = some (s, d, e)) :
      IsR trs cs ⟨.g i ph j, tdec .c s, tinc d e, .g i ph j⟩
  | next (i : ℕ) (t : KTr Q ι) (hi : trs[i]? = some t) (x : ι) (h : t.op = .zero x) (ph : Bool)
      (j : ℕ) (hj : j < (if ph then (zd cs x).l2 else (zd cs x).l1).length) :
      IsR trs cs ⟨.g i ph j, 0, 0, .g i ph (j + 1)⟩
  | sw (i : ℕ) (t : KTr Q ι) (hi : trs[i]? = some t) (x : ι) (h : t.op = .zero x) :
      IsR trs cs ⟨.g i false (zd cs x).l1.length, 0, 0, .g i true 0⟩
  | exit (i : ℕ) (t : KTr Q ι) (hi : trs[i]? = some t) (x : ι) (h : t.op = .zero x) :
      IsR trs cs ⟨.g i true (zd cs x).l2.length, Pi.single .b 1, 0, .main t.dst⟩

/-- The working counters. -/
def GW (cs : List ι) : Finset (Ct ι) :=
  ((Ct.a :: Ct.t :: Ct.u none :: (cs.map Ct.sim ++ cs.map (fun y => Ct.u (some y))))).toFinset

/-- The projection to the machine's counters. -/
def proj (w : Ct ι → ℕ) : ι → ℕ := fun y => w (.sim y)

theorem zd_wf {cs : List ι} (hcs : cs.Nodup) (x : ι) : (zd cs x).WF := by
  have hn : (cs.erase x).Nodup := hcs.erase x
  have hx : x ∉ cs.erase x := hcs.not_mem_erase
  simp only [ZD.WF, ZD.L, ZD.Z, zd, List.map_cons, List.map_map, Function.comp_def, uMap,
    List.cons_append, List.nodup_cons, List.mem_cons, List.mem_append, List.mem_map,
    List.nodup_append]
  refine ⟨by simp, by simp, ?_, by simp, by simp, hn.map (fun _ _ h => Ct.sim.inj h),
    ⟨by simp, hn.map (fun _ _ h => Option.some.inj (Ct.u.inj h))⟩, ?_⟩
  · simpa using hx
  · rintro _ ⟨y, -, rfl⟩ _ (rfl | ⟨z, -, rfl⟩) <;> simp

theorem mem_W_zd {cs : List ι} (hcs : cs.Nodup) {x : ι} (hx : x ∈ cs) (p : Ct ι) :
    p ∈ (zd cs x).W ↔ p ∈ GW cs ∧ p ≠ .u (some x) := by
  simp only [ZD.W, ZD.L, ZD.Z, zd, GW, List.mem_toFinset, List.mem_cons, List.mem_append,
    List.mem_map, List.map_cons, uMap]
  cases p with
  | sim y =>
    by_cases hyx : y = x
    · subst hyx; simp [hx]
    · simp [hyx, List.mem_erase_of_ne hyx]
  | a => simp
  | b => simp
  | c => simp
  | t => simp
  | u o =>
    cases o with
    | none => simp
    | some y =>
      by_cases hyx : y = x
      · subst hyx; simp [hcs.not_mem_erase]
      · simp [hyx, List.mem_erase_of_ne hyx]

/-- The global sum is the gadget's sum plus the temporary of the tested counter. -/
theorem sumW_GW {cs : List ι} (hcs : cs.Nodup) {x : ι} (hx : x ∈ cs) (w : Ct ι → ℕ) :
    sumW (GW cs) w = sumW (zd cs x).W w + w (.u (some x)) := by
  have hmem : Ct.u (some x) ∈ GW cs := by simp [GW, hx]
  have heq : GW cs = insert (Ct.u (some x)) (zd cs x).W := by
    ext p
    rw [Finset.mem_insert, mem_W_zd hcs hx]
    by_cases hp : p = .u (some x)
    · subst hp; simp [hmem]
    · simp [hp]
  have hnot : Ct.u (some x) ∉ (zd cs x).W := by rw [mem_W_zd hcs hx]; simp
  unfold sumW
  rw [heq, Finset.sum_insert hnot]
  ring

/-- Moving one unit inside the working counters keeps the sum. -/
theorem sumW_move {W : Finset (Ct ι)} {p q : Ct ι} (hp : p ∈ W) (hq : q ∈ W) {v : Ct ι → ℕ}
    (hv : 1 ≤ v p) : sumW W (v - Pi.single p 1 + Pi.single q 1) = sumW W v := by
  have h : (v - Pi.single p 1 + Pi.single q 1) + Pi.single p 1 = v + Pi.single q 1 := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    split_ifs with h1 h2 <;> subst_vars <;> omega
  have h3 : ∑ i ∈ W, ((v - Pi.single p 1 + Pi.single q 1 : Ct ι → ℕ) i +
      (Pi.single p 1 : Ct ι → ℕ) i) = ∑ i ∈ W, (v i + (Pi.single q 1 : Ct ι → ℕ) i) :=
    Finset.sum_congr rfl (fun i _ => congrFun h i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_pi_single',
    Finset.sum_pi_single'] at h3
  simp only [hp, hq, if_true] at h3
  unfold sumW
  omega

theorem flat_of_mem {cs : List ι} {x : ι} {l : List (Ct ι × Ct ι × Ct ι)}
    (hl : TWF Ct.c (zd cs x).W l) {s d e : Ct ι} (hm : (s, d, e) ∈ l) :
    Flat (tdec Ct.c s) (tinc d e) := by
  obtain ⟨-, hd, he⟩ := hl.mem _ hm
  obtain ⟨h1, h2⟩ := hl.src _ hm _ hm
  have hcW := hl.cW
  exact flat_t h1 h2 (fun h => hcW (h ▸ hd)) (fun h => hcW (h ▸ he))

variable (trs : List (KTr Q ι)) (cs : List ι) (qf : Q)

/-- **The goal at a control state of the machine.** -/
def GS (q : Q) (w : Ct ι → ℕ) : Prop :=
  (Holds (sumW (GW cs) w) (w .b) (w .c) ∨ Broken (sumW (GW cs) w) (w .b) (w .c)) →
    Holds (sumW (GW cs) w) (w .b) (w .c) ∧ KReach trs (w .b) (q, proj w) (qf, 0)

/-- **The goal inside a gadget**: the rest of the gadget, then the goal at its exit. -/
def Rest (i : ℕ) (ph : Bool) (j : ℕ) (v : Ct ι → ℕ) : Prop :=
  ∀ t x, trs[i]? = some t → t.op = .zero x →
    ∃ w1 w2, TSeq .c (if ph then [] else (zd cs x).l1.drop j) v w1 ∧
      TSeq .c (if ph then (zd cs x).l2.drop j else (zd cs x).l2) w1 w2 ∧ 1 ≤ w2 .b ∧
      GS trs cs qf t.dst (w2 - Pi.single .b 1)

/-- The goal at any control state. -/
def Phi : Cfg (CL Q) (Ct ι) → Prop
  | (.main q, w) => GS trs cs qf q w
  | (.g i ph j, w) => Rest trs cs qf i ph j w

variable {trs cs qf}

/-- The rules of the compiled system, as a set. -/
def RS (trs : List (KTr Q ι)) (cs : List ι) : Set (Rule (CL Q) (Ct ι)) := {ρ | IsR trs cs ρ}

theorem rest_unique {i : ℕ} {t t' : KTr Q ι} {x x' : ι} (hi : trs[i]? = some t)
    (hi' : trs[i]? = some t') (h : t.op = .zero x) (h' : t'.op = .zero x') : t' = t ∧ x' = x := by
  rw [hi] at hi'
  obtain rfl := Option.some.inj hi'
  rw [h] at h'
  exact ⟨rfl, (KOp.zero.inj h').symm⟩

/-- A final configuration. -/
structure IsFinal (w : Ct ι → ℕ) : Prop where
  hb : w .b = 0
  hc : w .c = 0
  hs : proj w = 0

/-- **The main induction.** -/
theorem phi_of_reach (hcs : cs.Nodup) (hall : ∀ y, y ∈ cs) {x y : Cfg (CL Q) (Ct ι)}
    (h : Reach (RS trs cs) x y) (hy : y.1 = .main qf) (hf : IsFinal y.2) : Phi trs cs qf x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨q, w⟩ := y
    simp only at hy hf; subst hy
    intro _
    refine ⟨by rw [hf.hb, hf.hc]; exact holds_end _, ?_⟩
    rw [hf.hb, hf.hs]; exact .refl _
  | head hs hr ih =>
    obtain ⟨ρ, hρ, v, hv⟩ := hs
    have hall' : ∀ y : ι, y ∈ cs := hall
    cases hρ with
    | nop t ht hop =>
      simp only [Phi, tsub_zero, add_zero] at ih ⊢
      intro hhb
      obtain ⟨h1, h2⟩ := ih hhb
      exact ⟨h1, by simpa using KReach.head (KStep.nop t ht hop _) h2⟩
    | inc t ht x hop =>
      simp only [Phi] at ih ⊢
      have ha1 : 1 ≤ v .a := by have := hv .a; simpa using this
      have e1 : sumW (GW cs) (v - Pi.single .a 1 + Pi.single (.sim x) 1) = sumW (GW cs) v :=
        sumW_move (by simp [GW]) (by simp [GW, hall]) ha1
      have e4 : proj (v - Pi.single .a 1 + Pi.single (.sim x) 1) =
          Function.update (proj v) x (proj v x + 1) := by
        funext y
        by_cases hyx : y = x
        · subst hyx; simp [proj, Pi.single_apply]
        · simp [proj, Pi.single_apply, hyx]
      unfold GS at ih ⊢
      simp only [e1, e4, Pi.add_apply, Pi.sub_apply, Pi.single_apply, reduceCtorEq, if_false,
        tsub_zero, add_zero] at ih
      intro hhb
      obtain ⟨h1, h2⟩ := ih hhb
      exact ⟨h1, by simpa using KReach.head (KStep.inc t ht x hop _) h2⟩
    | dec t ht x hop =>
      simp only [Phi] at ih ⊢
      have hx1 : 1 ≤ v (.sim x) := by have := hv (.sim x); simpa using this
      have e1 : sumW (GW cs) (v - Pi.single (.sim x) 1 + Pi.single .a 1) = sumW (GW cs) v :=
        sumW_move (by simp [GW, hall]) (by simp [GW]) hx1
      have e4 : proj (v - Pi.single (.sim x) 1 + Pi.single .a 1) =
          Function.update (proj v) x (proj v x - 1) := by
        funext y
        by_cases hyx : y = x
        · subst hyx; simp [proj, Pi.single_apply]
        · simp [proj, Pi.single_apply, hyx]
      unfold GS at ih ⊢
      simp only [e1, e4, Pi.add_apply, Pi.sub_apply, Pi.single_apply, reduceCtorEq, if_false,
        tsub_zero, add_zero] at ih
      intro hhb
      obtain ⟨h1, h2⟩ := ih hhb
      exact ⟨h1, by simpa using KReach.head (KStep.dec t ht x hop _ hx1) h2⟩
    | enter i t hi x hop =>
      simp only [Phi, tsub_zero, add_zero] at ih ⊢
      obtain ⟨w1, w2, h1, h2, hb2, hgs⟩ := ih t x hi hop
      simp only [Bool.false_eq_true, if_false, List.drop_zero] at h1 h2
      have hx : x ∈ cs := hall x
      have hwf := zd_wf hcs x
      obtain ⟨m1, m2, m3⟩ := ZD.zero_macro hwf h1 h2
      have hbW : Ct.b ∉ (zd cs x).W := by rw [mem_W_zd hcs hx]; simp [GW]
      have huW : Ct.u (some x) ∉ (zd cs x).W := by rw [mem_W_zd hcs hx]; simp
      have hbGW : Ct.b ∉ GW cs := by simp [GW]
      have hb1 : w1 .b = v .b := tseq_out (ZD.twf1 hwf) h1 hbW (by simp [zd])
      have hb2' : w2 .b = w1 .b := tseq_out (ZD.twf2 hwf) h2 hbW (by simp [zd])
      have hu1 : w1 (.u (some x)) = v (.u (some x)) := tseq_out (ZD.twf1 hwf) h1 huW (by simp [zd])
      have hu2 : w2 (.u (some x)) = w1 (.u (some x)) := tseq_out (ZD.twf2 hwf) h2 huW (by simp [zd])
      have gv := sumW_GW hcs hx v
      have gw := sumW_GW hcs hx w2
      set w3 := w2 - Pi.single Ct.b 1 with hw3
      have e3 : sumW (GW cs) w3 = sumW (GW cs) w2 := by
        unfold sumW
        refine Finset.sum_congr rfl fun i hi' => ?_
        have : i ≠ Ct.b := fun h => hbGW (h ▸ hi')
        simp [hw3, Pi.single_apply, this]
      have e3b : w3 .b = v .b - 1 := by simp [hw3, hb2', hb1]
      have e3c : w3 .c = w2 .c := by simp [hw3]
      have hvb : 1 ≤ v .b := by omega
      have m1' : sumW (zd cs x).W w2 + w2 .c = sumW (zd cs x).W v + v .c := m1
      have hle : sumW (GW cs) w3 ≤ 4 * sumW (GW cs) v := by omega
      have hsum : sumW (GW cs) w3 + w3 .c = sumW (GW cs) v + v .c := by omega
      unfold GS at hgs ⊢
      rw [e3, ← e3, e3b] at hgs
      intro hhb
      rcases hhb with hH | hB
      · by_cases heq : sumW (GW cs) w3 = 4 * sumW (GW cs) v
        · have hH3 := (holds_test_iff hvb hle hsum hH).mpr heq
          obtain ⟨-, hk⟩ := hgs (Or.inl hH3)
          have hS : sumW (zd cs x).W w2 = 4 * sumW (zd cs x).W v := by omega
          obtain ⟨hx0, hxx, hY⟩ := m3 hS
          have hp : proj w3 = proj v := by
            funext y
            by_cases hyx : y = x
            · subst hyx
              simpa [proj, hw3, Pi.single_apply, zd] using hxx
            · have hm : Ct.sim y ∈ (zd cs x).Y := by
                simp only [zd, List.mem_map]
                exact ⟨y, (List.mem_erase_of_ne hyx).mpr (hall y), rfl⟩
              simpa [proj, hw3, Pi.single_apply] using hY _ hm
          rw [hp] at hk
          refine ⟨hH, ?_⟩
          have ht : t ∈ trs := List.mem_of_getElem? hi
          have := KReach.head (KStep.zero t ht x hop (proj v) (by simpa [proj, zd] using hx0)) hk
          have e : 1 + (v .b - 1) = v .b := by omega
          rwa [e] at this
        · have hB3 := broken_test_of_holds hvb hle hsum hH heq
          exact absurd hB3 (not_holds_and_broken (hgs (Or.inr hB3)).1)
      · have hB3 := broken_test hvb hle hsum hB
        exact absurd hB3 (not_holds_and_broken (hgs (Or.inr hB3)).1)
    | loop i t hi x hop ph j s d e hj =>
      simp only [Phi] at ih ⊢
      intro t' x' hi' hop'
      obtain ⟨rfl, rfl⟩ := rest_unique hi hi' hop hop'
      obtain ⟨w1, w2, h1, h2, hb2, hgs⟩ := ih _ _ hi' hop'
      have hwf := zd_wf hcs x'
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hj
      have hdrop := List.drop_eq_getElem_cons hlt
      rw [hget] at hdrop
      have hmem : (s, d, e) ∈ (if ph then (zd cs x').l2 else (zd cs x').l1) :=
        List.mem_of_getElem? hj
      cases ph with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hdrop hmem h1 h2 ⊢
        have hf := flat_of_mem (ZD.twf1 hwf) hmem
        rw [hdrop] at h1 ⊢
        exact ⟨w1, w2, tseq_cons_step hf (by simpa using hv) (by simpa using h1), h2, hb2, hgs⟩
      | true =>
        simp only [if_true] at hdrop hmem h1 h2 ⊢
        have hf := flat_of_mem (ZD.twf2 hwf) hmem
        simp only [TSeq] at h1
        subst h1
        rw [hdrop] at h2 ⊢
        exact ⟨_, w2, rfl, tseq_cons_step hf (by simpa using hv) (by simpa using h2), hb2, hgs⟩
    | next i t hi x hop ph j hj =>
      simp only [Phi, tsub_zero, add_zero] at ih ⊢
      intro t' x' hi' hop'
      obtain ⟨rfl, rfl⟩ := rest_unique hi hi' hop hop'
      obtain ⟨w1, w2, h1, h2, hb2, hgs⟩ := ih _ _ hi' hop'
      have hdrop := List.drop_eq_getElem_cons hj
      cases ph with
      | false =>
        simp only [Bool.false_eq_true, if_false] at hdrop h1 h2 ⊢
        rw [hdrop]
        exact ⟨w1, w2, tseq_skip h1, h2, hb2, hgs⟩
      | true =>
        simp only [if_true] at hdrop h1 h2 ⊢
        rw [hdrop]
        exact ⟨w1, w2, h1, tseq_skip h2, hb2, hgs⟩
    | sw i t hi x hop =>
      simp only [Phi, tsub_zero, add_zero] at ih ⊢
      intro t' x' hi' hop'
      obtain ⟨rfl, rfl⟩ := rest_unique hi hi' hop hop'
      obtain ⟨w1, w2, h1, h2, hb2, hgs⟩ := ih _ _ hi' hop'
      simp only [if_true, List.drop_zero, TSeq] at h1 h2
      subst h1
      exact ⟨_, w2, by simp [TSeq], h2, hb2, hgs⟩
    | exit i t hi x hop =>
      simp only [Phi, add_zero] at ih ⊢
      intro t' x' hi' hop'
      obtain ⟨rfl, rfl⟩ := rest_unique hi hi' hop hop'
      have hb : 1 ≤ v .b := by have := hv .b; simpa using this
      refine ⟨v, v, rfl, ?_, hb, ih⟩
      simp [TSeq]

/-! ### Completeness -/

/-- The gadget's loops as runs of the compiled system. -/
theorem gadget_reach (hcs : cs.Nodup) {i : ℕ} {t : KTr Q ι} (hi : trs[i]? = some t) {x : ι}
    (hop : t.op = .zero x) (ph : Bool) :
    ∀ k j, (if ph then (zd cs x).l2 else (zd cs x).l1).length = j + k → ∀ {v w : Ct ι → ℕ},
      TSeq .c ((if ph then (zd cs x).l2 else (zd cs x).l1).drop j) v w →
      Reach (RS trs cs) (.g i ph j, v)
        (.g i ph (if ph then (zd cs x).l2 else (zd cs x).l1).length, w)
  | 0, j, hl, v, w, h => by
    rw [List.drop_eq_nil_of_le (by omega)] at h
    simp only [TSeq] at h
    subst h
    rw [hl, add_zero]
  | k + 1, j, hl, v, w, h => by
    have hlt : j < (if ph then (zd cs x).l2 else (zd cs x).l1).length := by omega
    have hdrop := List.drop_eq_getElem_cons hlt
    rcases hq : (if ph then (zd cs x).l2 else (zd cs x).l1)[j] with ⟨s, d, e⟩
    rw [hq] at hdrop
    rw [hdrop] at h
    obtain ⟨n, hn, ht⟩ := h
    have hj : (if ph then (zd cs x).l2 else (zd cs x).l1)[j]? = some (s, d, e) := by
      rw [List.getElem?_eq_getElem hlt, hq]
    have htwf : TWF Ct.c (zd cs x).W (if ph then (zd cs x).l2 else (zd cs x).l1) := by
      cases ph
      · exact ZD.twf1 (zd_wf hcs x)
      · exact ZD.twf2 (zd_wf hcs x)
    have hf := flat_of_mem htwf (List.mem_of_getElem? hj)
    have hloop : (⟨.g i ph j, tdec .c s, tinc d e, .g i ph j⟩ : Rule (CL Q) (Ct ι)) ∈ RS trs cs :=
      IsR.loop i t hi x hop ph j s d e hj
    have hnext : (⟨.g i ph j, 0, 0, .g i ph (j + 1)⟩ : Rule (CL Q) (Ct ι)) ∈ RS trs cs :=
      IsR.next i t hi x hop ph j hlt
    have hstep : Step (RS trs cs) (.g i ph j, itv (tdec .c s) (tinc d e) n v)
        (.g i ph (j + 1), itv (tdec .c s) (tinc d e) n v) := by
      have := Step.mk _ hnext (itv (tdec .c s) (tinc d e) n v) (by intro _; simp)
      simpa using this
    exact (iter_reach hloop hf v n hn).trans (Relation.ReflTransGen.head hstep
      (gadget_reach hcs hi hop ph k (j + 1) (by omega) ht))

/-- Empty temporaries. -/
def TZ (w : Ct ι → ℕ) : Prop := w .t = 0 ∧ ∀ o, w (.u o) = 0

theorem GW_nodup (hcs : cs.Nodup) :
    (Ct.a :: Ct.t :: Ct.u none :: (cs.map Ct.sim ++ cs.map (fun y => Ct.u (some y)))).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, List.mem_map, List.nodup_append]
  refine ⟨by simp, by simp, by simp, hcs.map (fun _ _ h => Ct.sim.inj h),
    hcs.map (fun _ _ h => Option.some.inj (Ct.u.inj h)), ?_⟩
  rintro _ ⟨y, -, rfl⟩ _ ⟨z, -, rfl⟩; simp

theorem sumW_GW_TZ (hcs : cs.Nodup) {w : Ct ι → ℕ} (hz : TZ w) :
    sumW (GW cs) w = w .a + (cs.map fun y => w (.sim y)).sum := by
  unfold sumW GW
  rw [List.sum_toFinset _ (GW_nodup hcs)]
  simp [hz.1, hz.2, Function.comp_def]

/-- One honest pass through the gadget. -/
theorem gadget_pass (hcs : cs.Nodup) (hall : ∀ y, y ∈ cs) {i : ℕ} {t : KTr Q ι}
    (hi : trs[i]? = some t) {x : ι} (hop : t.op = .zero x) {v : Ct ι → ℕ} (hx : v (.sim x) = 0)
    (hz : TZ v) (hH : Holds (sumW (GW cs) v) (v .b) (v .c)) (hb : 1 ≤ v .b) :
    ∃ w, Reach (RS trs cs) (.main t.src, v) (.main t.dst, w) ∧ proj w = proj v ∧ TZ w ∧
      w .b = v .b - 1 ∧ sumW (GW cs) w = 4 * sumW (GW cs) v ∧
      Holds (sumW (GW cs) w) (w .b) (w .c) ∧ v .a ≤ w .a := by
  have hxc : x ∈ cs := hall x
  have hwf := zd_wf hcs x
  have gv := sumW_GW hcs hxc v
  have hux : v (.u (some x)) = 0 := hz.2 _
  have hc3 : 3 * sumW (zd cs x).W v ≤ v (zd cs x).c := by
    have h4 : 4 ≤ 4 ^ v .b := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ v .b := Nat.pow_le_pow_right (by norm_num) hb
    unfold Holds at hH
    have h5 : sumW (GW cs) v * 4 ≤ sumW (GW cs) v * 4 ^ v .b := Nat.mul_le_mul_left _ h4
    show 3 * sumW (zd cs x).W v ≤ v Ct.c
    omega
  obtain ⟨w1, w2, h1, h2, hS, ht2, hu2⟩ := ZD.zero_honest hwf hx hz.1
    (fun z _ => by cases z <;> simp [zd, uMap, hz.2, hz.1]) hc3
  obtain ⟨m1, m2, m3⟩ := ZD.zero_macro hwf h1 h2
  obtain ⟨-, hxx, hY⟩ := m3 hS
  have hbW : Ct.b ∉ (zd cs x).W := by rw [mem_W_zd hcs hxc]; simp [GW]
  have huW : Ct.u (some x) ∉ (zd cs x).W := by rw [mem_W_zd hcs hxc]; simp
  have hbGW : Ct.b ∉ GW cs := by simp [GW]
  have hb1 : w1 .b = v .b := tseq_out (ZD.twf1 hwf) h1 hbW (by simp [zd])
  have hb2' : w2 .b = w1 .b := tseq_out (ZD.twf2 hwf) h2 hbW (by simp [zd])
  have hu1 : w1 (.u (some x)) = v (.u (some x)) := tseq_out (ZD.twf1 hwf) h1 huW (by simp [zd])
  have hu2' : w2 (.u (some x)) = w1 (.u (some x)) := tseq_out (ZD.twf2 hwf) h2 huW (by simp [zd])
  have gw := sumW_GW hcs hxc w2
  set w3 := w2 - Pi.single Ct.b 1 with hw3
  have e3 : sumW (GW cs) w3 = sumW (GW cs) w2 := by
    unfold sumW
    refine Finset.sum_congr rfl fun i hi' => ?_
    have : i ≠ Ct.b := fun h => hbGW (h ▸ hi')
    simp [hw3, Pi.single_apply, this]
  have hS3 : sumW (GW cs) w3 = 4 * sumW (GW cs) v := by omega
  have m1' : sumW (zd cs x).W w2 + w2 .c = sumW (zd cs x).W v + v .c := m1
  have hsum : sumW (GW cs) w3 + w3 .c = sumW (GW cs) v + v .c := by
    have : w3 .c = w2 .c := by simp [hw3]
    omega
  have e3b : w3 .b = v .b - 1 := by simp [hw3, hb2', hb1]
  have hH3 : Holds (sumW (GW cs) w3) (w3 .b) (w3 .c) := by
    rw [e3b]; exact (holds_test_iff hb (by omega) hsum hH).mpr hS3
  have hp : proj w3 = proj v := by
    funext y
    by_cases hyx : y = x
    · subst hyx
      simpa [proj, hw3, Pi.single_apply, zd] using hxx
    · have hm : Ct.sim y ∈ (zd cs x).Y := by
        simp only [zd, List.mem_map]
        exact ⟨y, (List.mem_erase_of_ne hyx).mpr (hall y), rfl⟩
      simpa [proj, hw3, Pi.single_apply] using hY _ hm
  have hz3 : TZ w3 := by
    refine ⟨by simpa [hw3] using ht2, fun o => ?_⟩
    rcases o with _ | y
    · simpa [hw3, zd, uMap] using hu2 Ct.a (List.mem_cons_self ..)
    · by_cases hyx : y = x
      · subst hyx; simp [hw3, hu2', hu1, hux]
      · have hm : Ct.sim y ∈ (zd cs x).Z := by
          simp only [ZD.Z, zd, List.mem_cons, List.mem_map]
          exact Or.inr ⟨y, (List.mem_erase_of_ne hyx).mpr (hall y), rfl⟩
        simpa [hw3, zd, uMap] using hu2 _ hm
  have ha : v .a ≤ w3 .a := by
    have s1 := sumW_GW_TZ hcs hz
    have s3 := sumW_GW_TZ hcs hz3
    have : (cs.map fun y => w3 (.sim y)) = cs.map fun y => v (.sim y) := by
      apply List.map_congr_left; intro y _; exact congrFun hp y
    rw [this] at s3
    omega
  refine ⟨w3, ?_, hp, hz3, e3b, hS3, hH3, ha⟩
  -- the run
  have r1 := gadget_reach hcs hi hop false (zd cs x).l1.length 0 (by simp) (v := v) (w := w1)
    (by simpa using h1)
  have r2 := gadget_reach hcs hi hop true (zd cs x).l2.length 0 (by simp) (v := w1) (w := w2)
    (by simpa using h2)
  simp only [Bool.false_eq_true, if_false, if_true] at r1 r2
  have s0 : Step (RS trs cs) (.main t.src, v) (.g i false 0, v) := by
    have := Step.mk (rs := RS trs cs) _ (IsR.enter i t hi x hop) v (by intro _; simp)
    simpa using this
  have s1 : Step (RS trs cs) (.g i false (zd cs x).l1.length, w1) (.g i true 0, w1) := by
    have := Step.mk (rs := RS trs cs) _ (IsR.sw i t hi x hop) w1 (by intro _; simp)
    simpa using this
  have s2 : Step (RS trs cs) (.g i true (zd cs x).l2.length, w2) (.main t.dst, w3) := by
    have := Step.mk (rs := RS trs cs) _ (IsR.exit i t hi x hop) w2
      (by intro p; by_cases hp' : p = .b <;> simp [Pi.single_apply, hp'] <;> omega)
    simpa [hw3] using this
  exact (Relation.ReflTransGen.head s0 r1).trans
    ((Relation.ReflTransGen.head s1 r2).tail s2)

/-- **The triple** `a = A`, `b = B`, `c = A·(4^B − 1)`. -/
def triple (A B : ℕ) : Ct ι → ℕ :=
  Pi.single .a A + Pi.single .b B + Pi.single .c (A * (4 ^ B - 1))

theorem sumW_triple (cs : List ι) (A B : ℕ) : sumW (GW cs) (triple A B) = A := by
  unfold sumW triple
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
  simp [GW]

/-- **CJLLO Lemma 7, soundness**: a run of the compiled system from a triple to a final
configuration gives a run of the machine with exactly `B` zero tests. -/
theorem sim_sound (hcs : cs.Nodup) (hall : ∀ y, y ∈ cs) {A B : ℕ} {q0 : Q} {wf : Ct ι → ℕ}
    (h : Reach (RS trs cs) (.main q0, triple A B) (.main qf, wf)) (hf : IsFinal wf) :
    KReach trs B (q0, 0) (qf, 0) := by
  have := phi_of_reach hcs hall h rfl hf
  simp only [Phi, GS] at this
  have hb : (triple A B : Ct ι → ℕ) .b = B := by simp [triple]
  have hc : (triple A B : Ct ι → ℕ) .c = A * (4 ^ B - 1) := by simp [triple]
  have hp : proj (triple A B : Ct ι → ℕ) = 0 := by funext y; simp [proj, triple]
  rw [sumW_triple, hb, hc, hp] at this
  exact (this (Or.inl (holds_triple A B))).2

/-- Runs with their length. -/
inductive KReachL (trs : List (KTr Q ι)) : ℕ → ℕ → Q × (ι → ℕ) → Q × (ι → ℕ) → Prop
  | refl (x : Q × (ι → ℕ)) : KReachL trs 0 0 x x
  | head {L m n : ℕ} {x y z : Q × (ι → ℕ)} : KStep trs m x y → KReachL trs L n y z →
      KReachL trs (L + 1) (m + n) x z

theorem KReach.withLen {n : ℕ} {x z : Q × (ι → ℕ)} (h : KReach trs n x z) :
    ∃ L, KReachL trs L n x z := by
  induction h with
  | refl x => exact ⟨0, .refl x⟩
  | head hs _ ih => obtain ⟨L, hL⟩ := ih; exact ⟨L + 1, .head hs hL⟩

/-- **The honest simulation of a run.** -/
theorem sim_run (hcs : cs.Nodup) (hall : ∀ y, y ∈ cs) {L n : ℕ} {x z : Q × (ι → ℕ)}
    (h : KReachL trs L n x z) : ∀ {w : Ct ι → ℕ}, proj w = x.2 → TZ w →
      Holds (sumW (GW cs) w) (w .b) (w .c) → w .b = n → L ≤ w .a →
      ∃ wf, Reach (RS trs cs) (.main x.1, w) (.main z.1, wf) ∧ proj wf = z.2 ∧ TZ wf ∧
        wf .b = 0 ∧ Holds (sumW (GW cs) wf) (wf .b) (wf .c) := by
  induction h with
  | refl x =>
    intro w hp hz hH hb _
    exact ⟨w, .refl, hp, hz, hb, hH⟩
  | @head L m n x y z hs hr ih =>
    intro w hp hz hH hb hL
    cases hs with
    | nop t ht hop v =>
      obtain ⟨wf, r, h1, h2, h3, h4⟩ := ih hp hz hH (by simpa using hb) (by omega)
      have s : Step (RS trs cs) (.main t.src, w) (.main t.dst, w) := by
        have := Step.mk (rs := RS trs cs) _ (IsR.nop t ht hop) w (by intro _; simp)
        simpa using this
      exact ⟨wf, .head s r, h1, h2, h3, h4⟩
    | inc t ht x' hop v =>
      change proj w = v at hp
      have ha : 1 ≤ w .a := by omega
      set w' := w - Pi.single Ct.a 1 + Pi.single (Ct.sim x') 1 with hw'
      have e1 : sumW (GW cs) w' = sumW (GW cs) w :=
        sumW_move (by simp [GW]) (by simp [GW, hall]) ha
      have hp' : proj w' = Function.update v x' (v x' + 1) := by
        funext y
        rw [← hp]
        by_cases hyx : y = x'
        · subst hyx; simp [hw', proj]
        · simp [hw', proj, Pi.single_apply, hyx]
      have hz' : TZ w' := ⟨by simp [hw', hz.1], fun o => by simp [hw', hz.2]⟩
      have hb' : w' .b = w .b := by simp [hw']
      have hc' : w' .c = w .c := by simp [hw']
      have ha' : w' .a = w .a - 1 := by simp [hw']
      obtain ⟨wf, r, h1, h2, h3, h4⟩ := ih hp' hz' (by rw [e1, hb', hc']; exact hH)
        (by rw [hb']; simpa using hb) (by omega)
      have s : Step (RS trs cs) (.main t.src, w) (.main t.dst, w') := by
        have := Step.mk (rs := RS trs cs) _ (IsR.inc t ht x' hop) w
          (by intro p; by_cases hpa : p = .a <;> simp [Pi.single_apply, hpa] <;> omega)
        simpa [hw'] using this
      exact ⟨wf, .head s r, h1, h2, h3, h4⟩
    | dec t ht x' hop v hv =>
      change proj w = v at hp
      have hx1 : 1 ≤ w (.sim x') := by rw [← hp] at hv; simpa [proj] using hv
      set w' := w - Pi.single (Ct.sim x') 1 + Pi.single Ct.a 1 with hw'
      have e1 : sumW (GW cs) w' = sumW (GW cs) w :=
        sumW_move (by simp [GW, hall]) (by simp [GW]) hx1
      have hp' : proj w' = Function.update v x' (v x' - 1) := by
        funext y
        rw [← hp]
        by_cases hyx : y = x'
        · subst hyx; simp [hw', proj]
        · simp [hw', proj, Pi.single_apply, hyx]
      have hz' : TZ w' := ⟨by simp [hw', hz.1], fun o => by simp [hw', hz.2]⟩
      have hb' : w' .b = w .b := by simp [hw']
      have hc' : w' .c = w .c := by simp [hw']
      have ha' : w' .a = w .a + 1 := by simp [hw']
      obtain ⟨wf, r, h1, h2, h3, h4⟩ := ih hp' hz' (by rw [e1, hb', hc']; exact hH)
        (by rw [hb']; simpa using hb) (by omega)
      have s : Step (RS trs cs) (.main t.src, w) (.main t.dst, w') := by
        have := Step.mk (rs := RS trs cs) _ (IsR.dec t ht x' hop) w
          (by intro p; by_cases hpa : p = .sim x' <;> simp [Pi.single_apply, hpa] <;> omega)
        simpa [hw'] using this
      exact ⟨wf, .head s r, h1, h2, h3, h4⟩
    | zero t ht x' hop v hv =>
      change proj w = v at hp
      obtain ⟨i, hi⟩ := List.getElem?_of_mem ht
      have hx0 : w (.sim x') = 0 := by rw [← hp] at hv; simpa [proj] using hv
      have hb1 : 1 ≤ w .b := by omega
      obtain ⟨w', r1, hp', hz', hb', -, hH', ha'⟩ := gadget_pass hcs hall hi hop hx0 hz hH hb1
      obtain ⟨wf, r, h1, h2, h3, h4⟩ := ih (by rw [hp', hp]) hz' hH' (by omega) (by omega)
      exact ⟨wf, r1.trans r, h1, h2, h3, h4⟩

/-- **CJLLO Lemma 7, completeness**: a run of the machine with exactly `B` zero tests gives a run
of the compiled system from a triple to a final configuration. -/
theorem sim_complete (hcs : cs.Nodup) (hall : ∀ y, y ∈ cs) {B : ℕ} {q0 : Q}
    (h : KReach trs B (q0, 0) (qf, 0)) :
    ∃ A wf, Reach (RS trs cs) (.main q0, triple A B) (.main qf, wf) ∧ IsFinal wf := by
  obtain ⟨L, hL⟩ := h.withLen
  have hp : proj (triple L B : Ct ι → ℕ) = 0 := by funext y; simp [proj, triple]
  have hz : TZ (triple L B : Ct ι → ℕ) := ⟨by simp [triple], fun o => by simp [triple]⟩
  obtain ⟨wf, r, h1, -, h3, h4⟩ := sim_run hcs hall hL (w := triple L B) hp hz
    (by rw [sumW_triple]; simpa [triple] using holds_triple L B) (by simp [triple])
    (by simp [triple])
  refine ⟨L, wf, r, ⟨h3, ?_, h1⟩⟩
  rw [h3] at h4
  unfold Holds at h4
  simp at h4
  omega

end Triple

end HTN
