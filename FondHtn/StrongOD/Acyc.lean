import FondHtn.StrongOD.AcycPot
/-!
# Strong OD plan existence of acyclic problems is in EXPSPACE ([CB21, Thm. 5.2], membership)

The game of `FondHtn/StrongOD/Play.lean` is started in the decomposition position
`(2, 0, s_I, tn_I)`: the existential player decomposes compound tasks (on descriptions,
`HTN.Article.decDesc`) until the network is primitive and then plays it
(`FOND.SOD.dec_sound`, `FOND.SOD.dec_complete`).  An acyclicity certificate `(R, rk)` of
polynomial size (`HTN.Article.exists_acycCert`) is guessed as part of the initial
configuration; it is carried along unchanged and makes the potential of
`FondHtn/StrongOD/AcycPot.lean` available: every reachable network has at most
`|T_I| · (B + 1) ^ (H + 1)` tasks (exponentially many), every decomposition sequence is at
most that long, so all configurations have exponential size and the depth budget
`2 · 2 ^ ((|p| + 5)(|p| + 6)) + 1` suffices.  The bounded-depth game tool
`HTN.Syn.PolyDom.inExpSpace_codeLang_of_game` gives

* **`FOND.strongOD_ACYC_mem`** — `PlanExFM strongOD ACYC ∈ EXPSPACE`.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.Article.NoHTN PTime FOND.Prim

namespace SOD

/-! ## The game with a certificate -/

/-- An acyclicity certificate: names and ranks. -/
abbrev ACert : Type := List ℕ × List (ℕ × ℕ)

/-- A configuration with a certificate. -/
abbrev ACfg : Type := ACert × GCfg

instance instDecEqACfg : DecidableEq ACfg :=
  @instDecidableEqProd _ _ (inferInstanceAs (DecidableEq ACert)) instDecEqGCfg

/-- Accepting configurations. -/
def accA (y : FProbDesc × ACfg) : Bool := gacc (y.1, y.2.2)

/-- Universal configurations. -/
def uniA (y : FProbDesc × ACfg) : Bool := guni (y.1, y.2.2)

/-- The successors: those of the game, with the certificate kept. -/
def succsA (y : FProbDesc × ACfg) : List ACfg := (gsuccs (y.1, y.2.2)).map fun c => (y.2.1, c)

/-- The certificate check: acyclicity, and the names and ranks among the numbers of `p`. -/
def certB (q : ProbDesc) (r : ACert) : Bool :=
  acycB q r && r.1.all (fun c => decide (c ∈ numsOf q)) &&
    decide (r.1.length ≤ (numsOf q).length) &&
    r.2.all (fun c => decide (c.1 ∈ numsOf q) && decide (c.2 ≤ (numsOf q).length)) &&
    decide (r.2.length ≤ (numsOf q).length)

/-- The initial configurations. -/
def initA (y : FProbDesc × ACfg) : Bool :=
  y.1.validB && certB (skel y.1) y.2.1 && decide (y.2.2 = (2, 0, y.1.init.dedup, d₀ y.1))

variable {p : FProbDesc}

theorem gameVal_lift : ∀ (k : ℕ) (r : ACert) (c : GCfg),
    gameVal accA uniA succsA p k (r, c) = gameVal gacc guni gsuccs p k c := by
  intro k
  induction k with
  | zero => intro r c; rfl
  | succ k ih =>
    intro r c
    show (gacc (p, c) || bif guni (p, c) then
        ((gsuccs (p, c)).map fun c => (r, c)).all (gameVal accA uniA succsA p k)
      else ((gsuccs (p, c)).map fun c => (r, c)).any (gameVal accA uniA succsA p k)) = _
    rw [List.all_map, List.any_map]
    have : (gameVal accA uniA succsA p k ∘ fun c => (r, c)) = gameVal gacc guni gsuccs p k :=
      funext fun c => ih r c
    rw [this]
    rfl

theorem gameReach_lift : ∀ (n : ℕ) (r : ACert) (c : GCfg) (y : ACfg),
    GameReach succsA p n (r, c) y → y.1 = r ∧ GameReach gsuccs p n c y.2 := by
  intro n
  induction n with
  | zero => rintro r c y rfl; exact ⟨rfl, rfl⟩
  | succ n ih =>
    rintro r c y ⟨c₁, h₁, hr⟩
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 h₁
    obtain ⟨h1, h2⟩ := ih r c' y hr
    exact ⟨h1, c', hc', h2⟩

/-! ## Polynomial time -/

theorem pt_skel : PT skel := by
  unfold skel
  exact PT.pair (PT.pair (PT.const []) (PT.snd.comp PT.fst))
    (PT.pair (PT.const []) (PT.pair (PT.snd.comp PT.snd) (PT.const _)))

theorem pt_certB : PT fun x : ProbDesc × ACert => certB x.1 x.2 := by
  have hN : PT fun x : ProbDesc × ACert => numsOf x.1 := pt_numsOf.comp PT.fst
  unfold certB
  exact PT.and (PT.and (PT.and (PT.and (pt_acycB.comp (PT.pair PT.fst PT.snd))
    (PT.all (PT.fst.comp PT.snd) (PT.elem (hN.comp PT.fst) PT.snd)))
    (PT.le (PT.length (PT.fst.comp PT.snd)) (PT.length hN)))
    (PT.all (PT.snd.comp PT.snd) (PT.and (PT.elem (hN.comp PT.fst) (PT.fst.comp PT.snd))
      (PT.le (PT.snd.comp PT.snd) (PT.length (hN.comp PT.fst))))))
    (PT.le (PT.length (PT.snd.comp PT.snd)) (PT.length hN))

theorem pt_initA : PT initA := by
  unfold initA
  exact PT.and (PT.and (FProbDesc.pt_validB.comp PT.fst)
    (pt_certB.comp (PT.pair (pt_skel.comp PT.fst) (PT.fst.comp PT.snd))))
    (PT.eq (PT.snd.comp PT.snd) (PT.pair (PT.const 2) (PT.pair (PT.const 0)
      (PT.pair (PT.dedup (PT.fst.comp (PT.snd.comp PT.fst))) (pt_d₀.comp PT.fst)))))

theorem pt_accA : PT accA := pt_gacc.comp (PT.pair PT.fst (PT.snd.comp PT.snd))

theorem pt_uniA : PT uniA := pt_guni.comp (PT.pair PT.fst (PT.snd.comp PT.snd))

theorem pt_succsA : PT succsA :=
  PT.map (pt_gsuccs.comp (PT.pair PT.fst (PT.snd.comp PT.snd)))
    (PT.pair (PT.fst.comp (PT.snd.comp PT.fst)) PT.snd)

/-- The exponent of the depth budget. -/
noncomputable def qDepth : Polynomial ℕ := (Polynomial.X + 5) * (Polynomial.X + 6)

theorem eval_qDepth (n : ℕ) : qDepth.eval n = (n + 5) * (n + 6) := by simp [qDepth]

theorem pt_encF : PT fun p : FProbDesc => (enc p : List Bool) := ⟨lift, uc_lift, fun _ => rfl⟩

theorem natOfBits_pow (l : List Unit) :
    natOfBits ((l.map fun _ => false) ++ [true]) = 2 ^ l.length := by
  rw [natOfBits_append, List.map_const', natOfBits_replicate_false, List.length_replicate]
  simp [natOfBits_cons]

theorem exists_pt_depth : ∃ depth : FProbDesc → ℕ, PT depth ∧
    ∀ p, depth p = 2 * 2 ^ ((sz p + 5) * (sz p + 6)) + 1 := by
  obtain ⟨g, hg, hglen⟩ := PolyDom.exists_pt_polyLen qDepth
  refine ⟨fun p => 2 * natOfBits (((g (enc p)).map fun _ => false) ++ [true]) + 1,
    PT.affine 2 1 (PT.ofBits (PT.append (PT.map (hg.comp pt_encF) (PT.const false))
      (PT.const [true]))), fun p => ?_⟩
  show 2 * natOfBits (((g (enc p)).map fun _ => false) ++ [true]) + 1 = _
  rw [natOfBits_pow, hglen, eval_qDepth]
  rfl

/-! ## Sizes -/

theorem sz_skel_le (p : FProbDesc) : sz (skel p) ≤ sz p + 4 := by
  obtain ⟨⟨a, m⟩, i, t⟩ := p
  simp only [skel, sz_prod, sz_nil, FProbDesc.methods, FProbDesc.tnI]
  have : sz (([] : List ℕ), ([] : List ℕ)) = 2 := rfl
  have := Prim.one_le_sz_list a
  have := Prim.one_le_sz_list i
  omega

/-- The invariant of the reachable configurations. -/
def AG (p : FProbDesc) (R : List ℕ) (rk : ℕ → ℕ) (Φ₀ : ℕ) (c : GCfg) : Prop :=
  c.1 ≤ 2 ∧ (c.1 = 1 → c.2.1 ∈ c.2.2.2.ids ∧ readyB c.2.2.2 c.2.1 = true) ∧
    (c.1 ≠ 1 → c.2.1 = 0) ∧ CfgInv (c.2.2.1, c.2.2.2) ∧ PGood R c.2.2.2 ∧
    pot (sz (skel p)) rk c.2.2.2 ≤ Φ₀ ∧ (∀ f ∈ c.2.2.1, f ∈ factsU p) ∧
    CfgNums (skel p) (Φ₀ + sz (skel p)) ([], c.2.2.2)

theorem AG_succ (hp : p.Valid) {R : List ℕ} {rk : ℕ → ℕ} (hcert : AcycCert (skel p) R rk)
    {Φ₀ : ℕ} {c c' : GCfg} (hc : AG p R rk Φ₀ c) (h : c' ∈ gsuccs (p, c)) : AG p R rk Φ₀ c' := by
  obtain ⟨t, x, s, d⟩ := c
  obtain ⟨ht, h1, hn1, hinv, hg, hpot, hsU, hN⟩ := hc
  simp only at ht h1 hn1 hinv hg hpot hsU hN
  have hB : ∀ e ∈ p.methods, e.2.ids.length ≤ sz (skel p) := methods_ids_le (p := skel p)
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
  · simp only [gsuccs, beq_self_eq_true, cond_true, playMoves, List.mem_map,
      List.mem_filter, Bool.and_eq_true] at h
    obtain ⟨y, ⟨hy, ⟨hr, -⟩, -⟩, rfl⟩ := h
    exact ⟨by norm_num, fun _ => ⟨hy, hr⟩, fun h => absurd rfl h, hinv, hg, hpot, hsU, hN⟩
  · simp only [gsuccs, show ((1 : ℕ) == 0) = false from rfl, cond_false, beq_self_eq_true,
      cond_true, outMoves, List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    obtain ⟨hx, hr⟩ := h1 rfl
    have hr' := (readyB_iff d x).1 hr
    obtain ⟨hg', hpot'⟩ := pot_progDesc (B := sz (skel p)) (rk := rk) hg x
    refine ⟨by norm_num, fun h => absurd h (by norm_num), fun _ => rfl,
      inv_progDesc hinv hx hr' (List.nodup_dedup _), hg', hpot'.trans hpot, fun f hf => ?_, ?_⟩
    · rw [List.mem_dedup] at hf
      simp only [nextL, List.mem_append, List.mem_filter] at hf
      rcases hf with ⟨hf, -⟩ | hf
      · exact hsU f hf
      · exact add_mem_factsU he hf
    · obtain ⟨n1, n2, -⟩ := hN
      exact ⟨fun y hy => n1 y (List.mem_filter.1 hy).1, fun q hq => n2 q (List.mem_filter.1 hq).1,
        fun f hf => by simp at hf⟩
  · simp only [gsuccs, show ((2 : ℕ) == 0) = false from rfl, show ((2 : ℕ) == 1) = false from rfl,
      cond_false] at h
    rcases mem_decMoves.1 h with ⟨y, hy, hb, e, he, he1, rfl⟩ | ⟨-, rfl⟩
    · have hl : lblOf d y = (true, e.1) := by rw [lblOf_eq_of_fst hb, he1]
      have hev := hp.methods e he
      obtain ⟨hg', hpot'⟩ := pot_decDesc hcert hB hinv hg hev hy hl he
      have hlen := ids_le_pot (B := sz (skel p)) (rk := rk) hg
      obtain ⟨n1, n2, -⟩ := hN
      refine ⟨le_rfl, fun h => absurd h (by norm_num), fun _ => rfl, inv_decDesc hinv hev, hg',
        hpot'.le.trans hpot, hsU, fun z hz => ?_, fun q hq => ?_, fun f hf => by simp at hf⟩
      · rcases List.mem_append.1 hz with hz | hz
        · exact n1 z (List.mem_filter.1 hz).1
        · right
          have := lt_of_mem_freshIds hz
          have := hB e he
          omega
      · rcases List.mem_append.1 hq with hq | hq
        · exact n2 q (List.mem_filter.1 hq).1
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hq
          exact mem_numsOf_method (p := skel p) he (List.mem_cons_of_mem _
            (List.mem_append_right _ (lblOf_mem hev hz)))
    · exact ⟨by norm_num, fun h => absurd h (by norm_num), fun _ => rfl, hinv, hg, hpot, hsU, hN⟩

theorem AG_reach (hp : p.Valid) {R : List ℕ} {rk : ℕ → ℕ} (hcert : AcycCert (skel p) R rk)
    {Φ₀ : ℕ} : ∀ (n : ℕ) (c c' : GCfg), AG p R rk Φ₀ c → GameReach gsuccs p n c c' →
      AG p R rk Φ₀ c' := by
  intro n
  induction n with
  | zero => rintro c c' hc rfl; exact hc
  | succ n ih =>
    rintro c c' hc ⟨c₁, h₁, hr⟩
    exact ih c₁ c' (AG_succ hp hcert hc h₁) hr

theorem AG_init (hp : p.Valid) {R : List ℕ} {rk : ℕ → ℕ} (hcert : AcycCert (skel p) R rk)
    {H : ℕ} (hH : ∀ c, rk c ≤ H) :
    AG p R rk (pot (sz (skel p)) rk (d₀ p)) ((2 : ℕ), (0 : ℕ), p.init.dedup, d₀ p) := by
  have hg := (pot_d₀ (B := sz (skel p)) (rk := rk) hp hcert hH).1
  refine ⟨by norm_num, fun h => absurd h (by norm_num), fun _ => rfl, inv_d₀ hp, hg, le_rfl,
    fun f hf => List.mem_append_left _ (List.mem_dedup.1 hf), fun x hx => ?_, fun q hq => ?_,
    fun f hf => by simp at hf⟩
  · exact Or.inl (mem_numsOf_tnI (p := skel p) (List.mem_append_left _ hx))
  · exact mem_numsOf_tnI (p := skel p) (List.mem_append_right _ (List.mem_map.2 ⟨q, hq, rfl⟩))

theorem length_flatMap_le' {β γ : Type} (l : List β) (f : β → List γ) (K : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ K) : (l.flatMap f).length ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := h x List.mem_cons_self
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [Nat.succ_mul]; omega

theorem sz_methods_le (p : FProbDesc) : sz p.methods ≤ sz p := by
  have := sz_snd_le p.1
  have := sz_fst_le p
  simp only [FProbDesc.methods] at *
  omega

section Bounds

variable {R : List ℕ} {rk : ℕ → ℕ} {Φ₀ : ℕ}

theorem sz_le_of_AG {c : GCfg} (hc : AG p R rk Φ₀ c) :
    sz c ≤ 100 * (Φ₀ + sz p + 6) ^ 3 := by
  obtain ⟨t, x, s, d⟩ := c
  obtain ⟨ht, h1, hn1, hinv, hg, hpot, hsU, hN⟩ := hc
  simp only at ht h1 hn1 hinv hg hpot hsU hN
  set Z := Φ₀ + sz p + 6 with hZ
  have hlen := (ids_le_pot (B := sz (skel p)) (rk := rk) hg).trans hpot
  have hinv' : CfgInv (([] : List ℕ), d) :=
    ⟨hinv.ids_nodup, hinv.lbl_mem, hinv.lbl_nodup, hinv.ord_nodup, List.nodup_nil, hinv.wf⟩
  have hd := sz_cfg_le_of hinv' hN hlen
  rw [sz_prod, sz_nil] at hd
  have hsk := sz_skel_le p
  have hZ1 : Φ₀ + sz (skel p) + 1 ≤ Z := by omega
  have hd' : 40 * (Φ₀ + sz (skel p) + 1) ^ 3 ≤ 40 * Z ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hZ1 3)
  have hx : sz x ≤ sz d + 1 := by
    by_cases h : t = 1
    · exact ((sz_le_of_mem (h1 h).1).trans (sz_ids_le_d d)).trans (Nat.le_succ _)
    · rw [hn1 h]; simp [sz_nat]
  have hU := sz_factsU_le p
  have hslen : s.length ≤ 2 * sz p :=
    ((hinv.st_nodup.subperm hsU).length_le).trans ((length_le_sz _).trans hU)
  have hs := sz_list_le s (2 * sz p) fun f hf => (sz_le_of_mem (hsU f hf)).trans hU
  have hm : s.length * (2 * (2 * sz p) + 2) ≤ 2 * sz p * (2 * (2 * sz p) + 2) :=
    Nat.mul_le_mul_right _ hslen
  have htag : sz t ≤ 5 := (sz_nat_le t).trans (by omega)
  have hZ6 : 6 ≤ Z := by omega
  have hpZ : sz p ≤ Z := by omega
  have hp2 : 2 * sz p * (2 * (2 * sz p) + 2) ≤ 8 * Z * Z := by nlinarith
  have hZ3 : Z * Z ≤ Z ^ 3 := by nlinarith
  simp only [sz_prod]
  nlinarith

theorem length_gsuccs_le_AG {c : GCfg} (hc : AG p R rk Φ₀ c) :
    (gsuccs (p, c)).length ≤ (Φ₀ + sz p + 6) ^ 2 := by
  obtain ⟨t, x, s, d⟩ := c
  obtain ⟨ht, h1, hn1, hinv, hg, hpot, hsU, hN⟩ := hc
  simp only at ht hg hpot
  have hlen := (ids_le_pot (B := sz (skel p)) (rk := rk) hg).trans hpot
  have hml : p.methods.length ≤ sz p := (length_le_sz _).trans (sz_methods_le p)
  have hsq : Φ₀ * sz p + 1 ≤ (Φ₀ + sz p + 6) ^ 2 := by nlinarith
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
  · simp only [gsuccs, beq_self_eq_true, cond_true, playMoves, List.length_map]
    have := List.length_filter_le (fun x => readyB d x && !(lblOf d x).1 &&
      appB p (lblOf d x).2 s) d.ids
    nlinarith
  · simp only [gsuccs, show ((1 : ℕ) == 0) = false from rfl, cond_false, beq_self_eq_true,
      cond_true, outMoves, List.length_map]
    have := length_effs_le p (lblOf d x).2
    nlinarith
  · simp only [gsuccs, show ((2 : ℕ) == 0) = false from rfl, show ((2 : ℕ) == 1) = false from rfl,
      cond_false, decMoves, List.length_append]
    have h1 := length_flatMap_le' d.ids (fun x => bif (lblOf d x).1 then
      (p.methods.filter fun e => e.1 == (lblOf d x).2).map fun e => ((2 : ℕ), (0 : ℕ), s,
        decDesc d x e) else []) (sz p) (fun x _ => by
          cases hb : (lblOf d x).1
          · simp [hb]
          · simp only [hb, cond_true, List.length_map]
            exact (List.length_filter_le _ _).trans hml)
    have h2 : (bif d.ids.all (fun x => !(lblOf d x).1) then [((0 : ℕ), (0 : ℕ), s, d)]
        else []).length ≤ 1 := by
      cases d.ids.all (fun x => !(lblOf d x).1) <;> simp
    have h3 : d.ids.length * sz p ≤ Φ₀ * sz p := Nat.mul_le_mul_right _ hlen
    omega

end Bounds

/-- The exponent of the size bound. -/
noncomputable def qA : Polynomial ℕ :=
  5 * ((Polynomial.X + 5) ^ 2 + Polynomial.X + 6) + 9

theorem eval_qA (n : ℕ) : qA.eval n = 5 * ((n + 5) ^ 2 + n + 6) + 9 := by simp [qA]

theorem pow_le_two_pow_mul (a b : ℕ) : a ^ b ≤ 2 ^ (a * b) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le b

theorem initA_iff (p : FProbDesc) (r : ACert) (c : GCfg) :
    initA (p, (r, c)) = true ↔ p.Valid ∧ certB (skel p) r = true ∧
      c = (2, 0, p.init.dedup, d₀ p) := by
  simp only [initA, Bool.and_eq_true, FProbDesc.validB_iff, decide_eq_true_eq, and_assoc]

theorem certB_iff (q : ProbDesc) (R : List ℕ) (rkL : List (ℕ × ℕ)) :
    certB q (R, rkL) = true ↔ AcycCert q R (kidOf rkL) ∧ (∀ c ∈ R, c ∈ numsOf q) ∧
      R.length ≤ (numsOf q).length ∧
      (∀ x ∈ rkL, x.1 ∈ numsOf q ∧ x.2 ≤ (numsOf q).length) ∧ rkL.length ≤ (numsOf q).length := by
  simp only [certB, Bool.and_eq_true, acycB_iff, List.all_eq_true, decide_eq_true_eq, and_assoc]

/-- The bounds of the game from a certified initial configuration. -/
theorem acyc_bounds (hp : p.Valid) {R : List ℕ} {rkL : List (ℕ × ℕ)}
    (hc : certB (skel p) (R, rkL) = true) :
    pot (sz (skel p)) (kidOf rkL) (d₀ p) ≤ 2 ^ ((sz p + 5) * (sz p + 6)) ∧
    sz ((R, rkL), ((2 : ℕ), (0 : ℕ), p.init.dedup, d₀ p)) ≤ 2 ^ qA.eval (sz p) ∧
    ∀ n (y : ACfg), GameReach succsA p n ((R, rkL), ((2 : ℕ), (0 : ℕ), p.init.dedup, d₀ p)) y →
      sz (succsA (p, y)) ≤ 2 ^ qA.eval (sz p) := by
  obtain ⟨hcert, hRN, hRl, hrkN, hrkl⟩ := (certB_iff _ _ _).1 hc
  set m := sz p with hm
  set H := (numsOf (skel p)).length with hHdef
  have hHs : H ≤ sz (skel p) := length_numsOf_le _
  have hsk := sz_skel_le p
  have hrk : ∀ c, kidOf rkL c ≤ H := kidOf_le fun q hq => (hrkN q hq).2
  set Φ₀ := pot (sz (skel p)) (kidOf rkL) (d₀ p) with hΦ₀
  have hpot := (pot_d₀ (B := sz (skel p)) hp hcert hrk).2
  have hlbl : p.tnI.lbl.length ≤ m := by
    have h1 := length_le_sz p.tnI.lbl
    have h2 := sz_tnI_le p
    have h3 : sz p.tnI.lbl ≤ sz p.tnI := (sz_snd_le p.tnI.2).trans (sz_snd_le p.tnI)
    omega
  -- the potential is exponential
  have hΦ : Φ₀ ≤ (m + 5) ^ (m + 6) := by
    have e1 : (sz (skel p) + 1) ^ (H + 1) ≤ (m + 5) ^ (m + 5) :=
      (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have e2 : p.tnI.lbl.length * (sz (skel p) + 1) ^ (H + 1) ≤ (m + 5) * (m + 5) ^ (m + 5) :=
      Nat.mul_le_mul (by omega) e1
    rw [pow_succ]
    linarith
  have hΦ2 : Φ₀ ≤ 2 ^ ((m + 5) * (m + 6)) := hΦ.trans (pow_le_two_pow_mul _ _)
  -- the size parameter
  set G := (m + 5) ^ 2 + m + 6 with hG
  set Z := Φ₀ + m + 6 with hZ
  have hZG : Z ≤ 2 ^ G := by
    have e1 : (m + 5) ^ (m + 6) ≤ 2 ^ ((m + 5) * (m + 6)) := pow_le_two_pow_mul _ _
    have e2 : m + 6 ≤ 2 ^ (m + 6) := (Nat.lt_two_pow_self).le
    have e3 : 2 ^ ((m + 5) * (m + 6)) + 2 ^ (m + 6) ≤ 2 ^ G := by
      have : (m + 5) * (m + 6) + 1 ≤ G := by rw [hG]; nlinarith
      have h4 : 2 ^ (m + 6) ≤ 2 ^ ((m + 5) * (m + 6)) := Nat.pow_le_pow_right (by norm_num)
        (by nlinarith)
      calc 2 ^ ((m + 5) * (m + 6)) + 2 ^ (m + 6) ≤ 2 ^ ((m + 5) * (m + 6) + 1) := by
            rw [pow_succ 2 ((m + 5) * (m + 6))]; omega
        _ ≤ 2 ^ G := Nat.pow_le_pow_right (by norm_num) this
    linarith
  have hZ6 : 6 ≤ Z := by omega
  have hq : 300 * Z ^ 5 ≤ 2 ^ qA.eval m := by
    rw [eval_qA, show 5 * ((m + 5) ^ 2 + m + 6) + 9 = 9 + 5 * G by rw [hG]; ring, pow_add,
      pow_mul']
    have : Z ^ 5 ≤ (2 ^ G) ^ 5 := Nat.pow_le_pow_left hZG 5
    have h512 : (300 : ℕ) ≤ 2 ^ 9 := by norm_num
    calc 300 * Z ^ 5 ≤ 2 ^ 9 * (2 ^ G) ^ 5 := Nat.mul_le_mul h512 this
      _ = 2 ^ 9 * (2 ^ G) ^ 5 := rfl
  -- the certificate
  have hr : sz (R, rkL) ≤ 40 * Z ^ 2 := by
    have := sz_rcert_le (H := H + 1) hRN hRl (fun q hq => ⟨(hrkN q hq).1,
      Nat.lt_succ_of_le (hrkN q hq).2⟩) hrkl
    have : 10 * (sz (skel p) + (H + 1) + 1) ^ 2 ≤ 40 * Z ^ 2 := by
      have : sz (skel p) + (H + 1) + 1 ≤ 2 * Z := by omega
      have h2 := Nat.pow_le_pow_left this 2
      rw [mul_pow] at h2
      norm_num at h2
      omega
    omega
  have hinit := AG_init hp hcert hrk
  have hZ1 : 1 ≤ Z := by omega
  have p2 : Z ^ 2 ≤ Z ^ 5 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have p3 : Z ^ 3 ≤ Z ^ 5 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have p4 : Z ^ 4 ≤ Z ^ 5 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have p0 : 1 ≤ Z ^ 5 := Nat.one_le_pow _ _ hZ1
  refine ⟨hΦ2, ?_, fun n y hy => ?_⟩
  · rw [sz_prod]
    have : sz ((2 : ℕ), (0 : ℕ), p.init.dedup, d₀ p) ≤ 100 * Z ^ 3 := sz_le_of_AG hinit
    omega
  · obtain ⟨hy1, hy2⟩ := gameReach_lift n _ _ y hy
    have hAG := AG_reach hp hcert n _ _ hinit hy2
    have hl : (gsuccs (p, y.2)).length ≤ Z ^ 2 := length_gsuccs_le_AG hAG
    have hel : ∀ c ∈ succsA (p, y), sz c ≤ 40 * Z ^ 2 + 100 * Z ^ 3 := by
      intro c hcm
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hcm
      rw [sz_prod, hy1]
      have : sz c' ≤ 100 * Z ^ 3 := sz_le_of_AG (AG_succ hp hcert hAG hc')
      omega
    have hs := sz_list_le _ _ hel
    have hlen : (succsA (p, y)).length ≤ Z ^ 2 := by
      unfold succsA; rw [List.length_map]; exact hl
    have e : (succsA (p, y)).length * (2 * (40 * Z ^ 2 + 100 * Z ^ 3) + 2) ≤
        Z ^ 2 * (2 * (40 * Z ^ 2 + 100 * Z ^ 3) + 2) := Nat.mul_le_mul_right _ hlen
    have : Z ^ 2 * (2 * (40 * Z ^ 2 + 100 * Z ^ 3) + 2) + 1 = 80 * Z ^ 4 + 200 * Z ^ 5 +
        2 * Z ^ 2 + 1 := by ring
    omega

end SOD

open SOD in
/-- **[CB21, Thm. 5.2], membership**: strong OD plan existence of acyclic problems is in
EXPSPACE. -/
theorem strongOD_ACYC_mem : Cx.EXPSPACE (PlanExFM .strongOD FClass.ACYC) := by
  obtain ⟨depth, hdPT, hdepth⟩ := exists_pt_depth
  refine inExpSpace_codeLang_of_game (α := FProbDesc) (σ := SOD.ACfg)
    (Q := fun p => p.Valid ∧ FClass.ACYC p.toProblem ∧ FMCrit.Solvable .strongOD p.toProblem)
    pt_initA pt_accA pt_uniA pt_succsA hdPT qA (fun p c₀ hi => ?_) (fun p => ?_)
  · obtain ⟨⟨R, rkL⟩, c⟩ := c₀
    obtain ⟨hv, hc, rfl⟩ := (initA_iff p _ _).1 hi
    obtain ⟨-, h1, h2⟩ := acyc_bounds hv hc
    exact ⟨h1, fun n _ y hy => h2 n y hy⟩
  · show (p.Valid ∧ FClass.ACYC p.toProblem ∧ p.toProblem.StrongODSolvable) ↔ _
    constructor
    · rintro ⟨hv, hac, hs⟩
      have hsv := strongDesc_valid hv
      obtain ⟨R, rkL, hab, hRN, hRl, hrkN, hrkl, -⟩ :=
        exists_acycCert hsv ((sMatches_ACYC p hv).1 hac)
      have hc : certB (skel p) (R, rkL) = true :=
        (certB_iff _ _ _).2 ⟨(acycB_iff _ _ _).1 hab, hRN, hRl, hrkN, hrkl⟩
      have hcert := ((certB_iff _ _ _).1 hc).1
      obtain ⟨hΦ, hsz, -⟩ := acyc_bounds hv hc
      refine ⟨((R, rkL), ((2 : ℕ), (0 : ℕ), p.init.dedup, d₀ p)), hsz,
        (initA_iff p _ _).2 ⟨hv, hc, rfl⟩, ?_⟩
      rw [gameVal_lift]
      rw [Problem.strongODSolvable_iff_fmSolvableDB] at hs
      obtain ⟨tn, ⟨hdec, hprim⟩, hbs⟩ := hs
      have hB : ∀ e ∈ p.methods, e.2.ids.length ≤ sz (skel p) := methods_ids_le (p := skel p)
      exact dec_complete hv (Good := PGood R) (Φ := pot (sz (skel p)) (kidOf rkL))
        (fun d hg => ids_le_pot hg)
        (fun s d x e hc' hg hx hl he => pot_decDesc hcert hB hc' hg (hv.methods e he) hx hl he)
        hprim hbs hdec (TnDesc.toTaskNetwork_wf _) id p.init.dedup (d₀ p) _
        (isoVia_id_of_agree (agree_d₀ hv)) (setOf_mem_dedup _).symm (inv_d₀ hv)
        (pot_d₀ (B := sz (skel p)) hv hcert (kidOf_le fun q hq => (hrkN q hq).2)).1 (by rw [hdepth]; omega)
    · rintro ⟨⟨⟨R, rkL⟩, c⟩, -, hi, hw⟩
      obtain ⟨hv, hc, rfl⟩ := (initA_iff p _ _).1 hi
      have hcert := ((certB_iff _ _ _).1 hc).1
      refine ⟨hv, (sMatches_ACYC p hv).2 (AcycCert.isACYC (p := strongDesc p) ⟨hcert.1, hcert.2⟩), ?_⟩
      rw [gameVal_lift] at hw
      obtain ⟨tn, hdec, hprim, hbs⟩ := dec_sound hv _ 0 _ _ (inv_d₀ hv) _ (agree_d₀ hv) hw
      rw [setOf_mem_dedup] at hbs
      exact Problem.strongODSolvable_iff_fmSolvableDB.2 ⟨tn, ⟨hdec, hprim⟩, hbs⟩

end FOND
