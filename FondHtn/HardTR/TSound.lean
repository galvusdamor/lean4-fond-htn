import FondHtn.HardTR.TLang
/-!
# CB22 Thm 5: soundness of the description

**`FOND.HardTR.TD.sound`**: if the described problem has a strong method-based policy, the boot
round of the tableau transducer is won, so some accepting claim at the top time is true.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TD

open TL TT TE HardMP HTN HTN.Syn HTN.Article AcycHard.Sav

variable {S : Type} {cS : S → ℕ} {X : Spec S} {allS : List S} {ops : List Op} {ens : List (En S)}
  {σ₀ : S}

/-! ## The initial state -/

theorem fv_r₀ (t x : ℕ) :
    fv cS (r₀ σ₀) t x = decide (Nat.pair t x ∈ bootFields cS σ₀) := by
  rcases t with _ | _ | _ | _ | _ | _ | _ | _ | t <;>
    simp [fv, r₀, g0, bootFields, fPh, fB, fSg, fGs, fCl, fCh, fSc, Nat.pair_eq_pair, bval, dsym,
      codePh, codeGs, codeOrd]
  rcases x with _ | _ | _ | _ | _ | _ | _ | x <;> simp [bvalT]

theorem val_r₀ (f : ℕ) : (toCfg cS (r₀ σ₀)).val f = decide (f ∈ bootFields cS σ₀) := by
  have := fv_r₀ (cS := cS) (σ₀ := σ₀) (Nat.unpair f).1 (Nat.unpair f).2
  rw [Nat.pair_unpair] at this
  exact this

theorem init_enc : (desc cS X allS ops ens σ₀).toProblem.init = (toCfg cS (r₀ σ₀)).enc := by
  ext y
  simp only [FProbDesc.toProblem, init_desc, Set.mem_setOf_eq, List.mem_cons, List.mem_map,
    Cfg.enc, Set.mem_union, Set.mem_singleton_iff, toCfg_cur, val_r₀, decide_eq_true_eq]
  constructor
  · rintro (rfl | ⟨f, hf, rfl⟩)
    · exact Or.inr rfl
    · exact Or.inl ⟨f, hf, rfl⟩
  · rintro (⟨f, hf, rfl⟩ | rfl)
    · exact Or.inr ⟨f, hf, rfl⟩
    · exact Or.inl rfl

theorem good_r₀ : Good X (r₀ σ₀) where
  c_lt := Nat.two_pow_pos _
  wb_lt k h := by cases h; simp [mm]
  rb_lt k h := by cases h
  gs_lt ℓ h := by cases h
  s_le := Nat.zero_le _

/-! ## The actions of the described problem -/

theorem δ_desc (hS : Function.Injective cS) {a : Act Op (En S)} (ha : a ∈ acts X ops ens) :
    (desc cS X allS ops ens σ₀).toProblem.δ (nmA cS a) = (toFAct (nmA cS a) (aspec cS X allS a)).toAction := by
  have h := FProbDesc.δ_of_mem (valid cS X allS ops ens σ₀ hS)
    ((mem_actions cS X allS ops ens σ₀).2 ⟨a, ha, rfl⟩)
  exact h

theorem aspec_wf (a : Act Op (En S)) : (aspec cS X allS a).WF := by
  cases a <;> simp [aspec, ASpec.WF, ASpec.cnew]

theorem outcomes_ne {d : FProbDesc} (hv : d.Valid) (x : ℕ) (s : Set ℕ)
    (_ : (d.toProblem.δ x).Applicable s) : ((d.toProblem.δ x).outcomes s).Nonempty := by
  obtain ⟨⟨e, he⟩, -⟩ := FProbDesc.δ_wf hv x
  exact ⟨_, e, he, rfl⟩

/-! ## Soundness -/

/-- **Soundness**: a strong method-based policy gives a won boot round of the transducer. -/
theorem sound (hS : Function.Injective cS) (hall : ∀ s, s ∈ allS) (hX : X.Valid)
    (h : (desc cS X allS ops ens σ₀).toProblem.MPStrongSolvable) :
    X.mach.Win {cfg true 0 0} (r₀ σ₀) := by
  set d := desc cS X allS ops ens σ₀ with hd
  have hv := valid cS X allS ops ens σ₀ hS
  have hP := FProbDesc.toProblem_wf hv
  have h' := (Problem.mpStrongSolvable_iff_mpProg hP).1 h
  have hL := lwin_of_mpProg_init hP h'
  have hD : (skelAt d.toProblem d.toProblem.tnI).domain.methods =
      {m | ∃ e ∈ meths cS X ops ens, e.toMethod = m} := by
    simp only [skelAt, Problem.skeleton, Problem.domain, FProbDesc.toProblem, hd, methods_desc]
  have hmwf : ∀ m ∈ (skelAt d.toProblem d.toProblem.tnI).domain.methods, m.subtasks.WF := by
    rw [hD]; rintro m ⟨e, -, rfl⟩; exact TnDesc.toTaskNetwork_wf _
  have htn : d.toProblem.tnI = (seqTn [lN .main]).toTaskNetwork := by
    simp only [FProbDesc.toProblem, hd, tnI_desc]
  have hgw : ∀ as ∈ {as | (skelAt d.toProblem d.toProblem.tnI).domain.NetYield d.toProblem.tnI as},
      GW cS X ops ens .main as := by
    intro as has
    rw [Set.mem_setOf_eq, htn] at has
    exact netYield_gen hmwf hD has
  have hpull := lwin_pull (appB := X.mach.app) (outsB := X.mach.outs) (nmA cS) (nmA_inj hS)
    (fun r => (toCfg cS r).enc) (Good X) (· ∈ acts X ops ens)
    (fun x s hx => outcomes_ne hv x s hx)
    (fun b t hb hG => by
      rw [δ_desc hS hb, applicable_enc, app_iff hS hX hG])
    (fun b t hb hG happ => by
      rw [δ_desc hS hb, outcomes_enc _ (aspec_wf b) ((app_iff hS hX hG b).2 happ),
        out_eq hall hG happ, Set.image_image])
    (fun b t t' hG happ ht' => good_out hX hG happ ht')
    hL (fun w hw x hx => by
      obtain ⟨u, -, rfl, hu⟩ := hgw w hw
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      exact ⟨b, hu b hb, rfl⟩)
    good_r₀ (init_enc (allS := allS) (ops := ops) (ens := ens))
  have hC : (⟨fun _ => 0, true⟩ : TL.Cfg) = cfg true 0 0 := by
    unfold cfg; congr 1; funext q; split_ifs <;> rfl
  refine NWin.toSWin (fun a s ha => X.mach.outs_nonempty a s ha) (T := X.mach.lts) (nwin_of_lwin hpull ?_)
  intro w hw
  obtain ⟨u, hu, hwu, -⟩ := hgw _ hw
  have : w = u := List.map_injective_iff.2 (nmA_inj hS) hwu
  subst this
  exact ⟨_, hC ▸ rfl, Mach.gen_main_acc (by simp [Spec.mach]) hu⟩

end TD

end HardTR

end FOND
