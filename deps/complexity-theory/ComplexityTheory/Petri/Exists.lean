import ComplexityTheory.Petri.Pres
/-!
# Existence of refutations

**Every unsolvable well-formed generalised problem has a refutation tree**
(`refutable_of_not_solvable`), by well-founded induction on the rank: a block that is not strongly
connected is pruned or split; a problem without characteristic solution is a leaf; a bounded
variable is eliminated; a failing pumping condition is removed by step (d); otherwise the problem
is perfect, hence solvable by Lambert's theorem.

Together with `Refutable.not_solvable`: for well-formed problems,
`¬ Solvable bs ↔ Refutable bs` (`not_solvable_iff_refutable`).
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp Classical

variable {ι : Type*} [Fintype ι]

/-- The induction hypothesis of the existence proof. -/
abbrev IHyp (bs : List (Block ι)) : Prop :=
  ∀ bs' : List (Block ι), Multiset.IsDershowitzMannaLT (grank bs') (grank bs) → (∀ g ∈ bs', Inv g) →
    ¬ Solvable bs' → Refutable bs'

theorem ih_alts {pre post : List (Block ι)} {b : Block ι} (IH : IHyp (pre ++ b :: post))
    (hI : ∀ g ∈ pre ++ b :: post, Inv g) {As : List (List (Block ι))}
    (hpres : ∀ A ∈ As, ∀ g ∈ A, Inv g ∧ brank g < brank b)
    (hsound : ∀ A ∈ As, Solvable (pre ++ A ++ post) → Solvable (pre ++ b :: post))
    (hns : ¬ Solvable (pre ++ b :: post)) : ∀ A ∈ As, Refutable (pre ++ A ++ post) := by
  intro A hA
  refine IH _ (grank_lt pre post A b fun g hg => (hpres A hA g hg).2) (fun g hg => ?_)
    (fun hs => hns (hsound A hA hs))
  simp only [List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact hI g (by simp [hg])
  · exact (hpres A hA g hg).1
  · exact hI g (by simp [hg])

theorem sound_of_iff {pre post : List (Block ι)} {b : Block ι} {As : List (List (Block ι))}
    (h : Solvable (pre ++ b :: post) ↔ ∃ A ∈ As, Solvable (pre ++ A ++ post)) :
    ∀ A ∈ As, Solvable (pre ++ A ++ post) → Solvable (pre ++ b :: post) :=
  fun A hA hs => h.2 ⟨A, hA, hs⟩

/-! ### Structural steps -/

theorem refute_not_sc {pre post : List (Block ι)} {b : Block ι} (IH : IHyp (pre ++ b :: post))
    (hI : ∀ g ∈ pre ++ b :: post, Inv g) (hns : ¬ Solvable (pre ++ b :: post))
    (hsc : ¬ SC b.comp) : Refutable (pre ++ b :: post) := by
  have hb := hI b (by simp)
  have hW := hb.1.1
  have hWe := (wf_iff.1 hW).1
  have he := hW.2.1
  let R := b.comp.nodes.filter fun v => ∃ es, TWalk b.comp.edges b.comp.entry es v
  let S := b.comp.nodes.filter fun v => ∃ es, TWalk b.comp.edges v es b.comp.entry
  have hR : b.comp.entry ∈ R := List.mem_filter.2 ⟨he, decide_eq_true ⟨[], TWalk.nil _⟩⟩
  have hS : b.comp.entry ∈ S := List.mem_filter.2 ⟨he, decide_eq_true ⟨[], TWalk.nil _⟩⟩
  have hRcl : ∀ e ∈ b.comp.edges, e.1 ∈ R → e.2.2 ∈ R := by
    intro e hE h1
    obtain ⟨-, h1⟩ := List.mem_filter.1 h1
    obtain ⟨es, hes⟩ := of_decide_eq_true h1
    exact List.mem_filter.2 ⟨(hWe e hE).2,
      decide_eq_true ⟨es ++ [e], hes.append (TWalk.cons hE (TWalk.nil _))⟩⟩
  have hScl : ∀ e ∈ b.comp.edges, e.2.2 ∈ S → e.1 ∈ S := by
    intro e hE h1
    obtain ⟨-, h1⟩ := List.mem_filter.1 h1
    obtain ⟨es, hes⟩ := of_decide_eq_true h1
    exact List.mem_filter.2 ⟨(hWe e hE).1, decide_eq_true ⟨e :: es, TWalk.cons hE hes⟩⟩
  by_cases hRp : ∃ v ∈ b.comp.nodes, v ∉ R
  · refine Refutable.prune R hR hRcl (ih_alts IH hI (prune_pres hb R hR hRp) ?_ hns)
    exact sound_of_iff (solvable_replace pre post b _ (prune_valid (R := (· ∈ R)) hR hRcl))
  by_cases hSp : ∃ v ∈ b.comp.nodes, v ∉ S
  · refine Refutable.split S hS hScl (ih_alts IH hI (split_pres hb S hS hSp) ?_ hns)
    exact sound_of_iff (solvable_replace pre post b _ (split_valid (S := (· ∈ S)) hS hScl))
  exfalso
  apply hsc
  push_neg at hRp hSp
  intro u hu v hv
  obtain ⟨-, hu'⟩ := List.mem_filter.1 (hSp u hu)
  obtain ⟨-, hv'⟩ := List.mem_filter.1 (hRp v hv)
  obtain ⟨es, hes⟩ := of_decide_eq_true hu'
  obtain ⟨es', hes'⟩ := of_decide_eq_true hv'
  obtain ⟨π, hπ, -⟩ := (hes.append hes').toIdx (C := b.comp)
  exact ⟨π, hπ⟩

/-! ### Bounded variables -/

theorem fib_nodup {C : Comp ι} (hN : C.edges.Nodup) {k : ℕ} (hk : k < C.edges.length)
    (ψ : ℕ → ℕ) : fib C (C.edge k) ψ = ψ k := by
  unfold fib
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hk) fun k' hk' hne => ?_]
  · simp
  · rw [if_neg]
    intro h
    apply hne
    have hk'' := Finset.mem_range.1 hk'
    unfold Comp.edge at h
    rw [List.getD_eq_getElem _ _ hk'', List.getD_eq_getElem _ _ hk] at h
    exact (hN.getElem_inj_iff).1 h

theorem getD_of_mem_getElem? {ts : List (Tri ι)} {i : ℕ} {t : Tri ι} (h : t ∈ ts[i]?) :
    ts.getD i Tri.zero = t := by
  rw [List.getD_eq_getElem?_getD, Option.mem_def.1 h]
  rfl

theorem decomp_at (bs : List (Block ι)) {i : ℕ} (hi : i < bs.length) :
    bs = bs.take i ++ bs[i] :: bs.drop (i + 1) ∧ (bs.take i).length = i := by
  refine ⟨?_, by simp; omega⟩
  conv_lhs => rw [← List.take_append_drop i bs]
  rw [List.drop_eq_getElem_cons hi]

theorem refute_bounded {bs : List (Block ι)} (IH : IHyp bs) (hI : ∀ g ∈ bs, Inv g)
    (hns : ¬ Solvable bs) {v : ℕ × (ι ⊕ ℕ ⊕ ι)} (hv : Req bs v) {B : ℤ}
    (hB : ∀ ts, CharSol bs ts → crd ts v ≤ B) : Refutable bs := by
  obtain ⟨i, w⟩ := v
  have hi : i < bs.length := by rcases w with j | k | j <;> exact hv.1
  obtain ⟨hbs, hlen⟩ := decomp_at bs hi
  have hv' : match w with
      | .inl j => bs[i].inp j = ⊤
      | .inr (.inl k) => k < bs[i].comp.edges.length
      | .inr (.inr j) => bs[i].out j = ⊤ := by
    rcases w with j | k | j <;> exact hv.2
  set pre := bs.take i
  set post := bs.drop (i + 1)
  set b := bs[i]
  rw [hbs] at IH hI hns hB ⊢
  have hb := hI b (by simp)
  have hget : ∀ ts : List (Tri ι), ∀ t ∈ ts[pre.length]?, ts.getD i Tri.zero = t := fun ts t ht => by
    rw [hlen] at ht; exact getD_of_mem_getElem? ht
  rcases w with j | k | j
  · have hj : b.inp j = ⊤ := hv'
    have hQ : ∀ ts, CharSol (pre ++ b :: post) ts → ∀ t ∈ ts[pre.length]?, t.M₁ j ≤ B.toNat :=
      fun ts hts t ht => by
        have := hB ts hts; simp only [crd, hget ts t ht] at this; omega
    refine Refutable.inp j B.toNat hj hQ (ih_alts IH hI (inp_pres hb hj _) ?_ hns)
    exact sound_of_iff (solvable_replace_of_bound pre post b _ (fun t => t.M₁ j ≤ B.toNat) hQ
      (fun t ht hq => inp_local _ t ht hq) (inp_local' hj _))
  · letI : ∀ a c : ι → ℤ, Decidable (a = c) := fun a c => Classical.propDecidable _
    have hk : k < b.comp.edges.length := hv'
    have he := edge_mem (C := b.comp) hk
    have hQ : ∀ ts, CharSol (pre ++ b :: post) ts → ∀ t ∈ ts[pre.length]?,
        fib b.comp (b.comp.edge k) t.ψ ≤ B.toNat := fun ts hts t ht => by
      rw [fib_nodup hb.2 hk]
      have := hB ts hts; simp only [crd, hget ts t ht] at this; omega
    refine Refutable.edge _ B.toNat he hQ (ih_alts IH hI (edge_pres hb he _) ?_ hns)
    exact sound_of_iff (solvable_replace_of_bound pre post b _
      (fun t => fib b.comp (b.comp.edge k) t.ψ ≤ B.toNat) hQ
      (fun t ht hq => edge_local he _ t ht hq) (edge_local' he _))
  · have hj : b.out j = ⊤ := hv'
    have hQ : ∀ ts, CharSol (pre ++ b :: post) ts → ∀ t ∈ ts[pre.length]?, t.M' j ≤ B.toNat :=
      fun ts hts t ht => by
        have := hB ts hts; simp only [crd, hget ts t ht] at this; omega
    refine Refutable.out j B.toNat hj hQ (ih_alts IH hI (out_pres hb hj _) ?_ hns)
    exact sound_of_iff (solvable_replace_of_bound pre post b _ (fun t => t.M' j ≤ B.toNat) hQ
      (fun t ht hq => out_local _ t ht hq) (out_local' hj _))

/-! ### Pumping -/

theorem refute_pumpF {pre post : List (Block ι)} {b : Block ι} (IH : IHyp (pre ++ b :: post))
    (hI : ∀ g ∈ pre ++ b :: post, Inv g) (hns : ¬ Solvable (pre ++ b :: post))
    (hsc : SC b.comp) (hP : ¬ PumpF b) : Refutable (pre ++ b :: post) := by
  have hb := hI b (by simp)
  obtain ⟨Ns, hD, hNs⟩ := exists_dcert hb.1 hsc hP
  refine Refutable.dF Ns hb.1.2.2.1 hD (ih_alts IH hI (dF_pres hNs hb) ?_ hns)
  exact sound_of_iff (solvable_replace pre post b _ (d_valid' hb.1.2.2.1 hD))

theorem refute_pumpB {pre post : List (Block ι)} {b : Block ι} (IH : IHyp (pre ++ b :: post))
    (hI : ∀ g ∈ pre ++ b :: post, Inv g) (hns : ¬ Solvable (pre ++ b :: post))
    (hsc : SC b.comp) (hP : ¬ PumpB b) : Refutable (pre ++ b :: post) := by
  have hb := hI b (by simp)
  obtain ⟨Ns, hD, hNs⟩ := exists_dcert (wfb_rev hb.1) (sc_rev hsc) (fun h => hP (pumpB_of_rev h))
  refine Refutable.dB Ns hb.1.2.2.2 hD (ih_alts IH hI (dB_pres hNs hb) ?_ hns)
  exact sound_of_iff (solvable_replace pre post b _
    (dB_valid (d_valid' (b := b.rev) hb.1.2.2.2 hD)))

/-! ### The existence theorem -/

theorem refute_step (bs : List (Block ι)) (IH : IHyp bs) (hI : ∀ g ∈ bs, Inv g)
    (hns : ¬ Solvable bs) : Refutable bs := by
  -- structural decomposition
  by_cases hsc : ∃ b ∈ bs, ¬ SC b.comp
  · obtain ⟨b, hb, hsc⟩ := hsc
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
    exact refute_not_sc IH hI hns hsc
  push_neg at hsc
  -- no characteristic solution
  by_cases hc : ∃ ts, CharSol bs ts
  swap
  · exact Refutable.noChar hc
  -- bounded variables
  by_cases hbd : ∃ v, Req bs v ∧ ∃ B : ℤ, ∀ ts, CharSol bs ts → crd ts v ≤ B
  · obtain ⟨v, hv, B, hB⟩ := hbd
    exact refute_bounded IH hI hns hv hB
  push_neg at hbd
  obtain ⟨hs, hH, hF⟩ := exists_full (bs := bs) fun v hv B => by
    obtain ⟨ts, h1, h2⟩ := hbd v hv B
    exact ⟨ts, h1, h2⟩
  -- pumping conditions
  by_cases hpf : ∃ b ∈ bs, ¬ PumpF b
  · obtain ⟨b, hb, hP⟩ := hpf
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
    exact refute_pumpF IH hI hns (hsc b hb) hP
  by_cases hpb : ∃ b ∈ bs, ¬ PumpB b
  · obtain ⟨b, hb, hP⟩ := hpb
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
    exact refute_pumpB IH hI hns (hsc b hb) hP
  push_neg at hpf hpb
  -- perfect
  exfalso
  obtain ⟨ts, hts⟩ := hc
  exact hns (solvable_of_perfect ⟨fun b hb => ⟨(hI b hb).1, hsc b hb, hpf b hb, hpb b hb⟩,
    ts, hs, hts, hH, hF⟩)

/-- **Existence of refutations.** -/
theorem refutable_of_not_solvable (bs : List (Block ι)) (hI : ∀ g ∈ bs, Inv g)
    (hns : ¬ Solvable bs) : Refutable bs := by
  refine (InvImage.wf grank Multiset.wellFounded_isDershowitzMannaLT).induction
    (C := fun bs => (∀ g ∈ bs, Inv g) → ¬ Solvable bs → Refutable bs) bs ?_ hI hns
  intro bs ih hI hns
  exact refute_step bs (fun bs' h => ih bs' h) hI hns

/-- **Characterisation of unsolvability** for well-formed generalised problems. -/
theorem not_solvable_iff_refutable (bs : List (Block ι)) (hI : ∀ g ∈ bs, Inv g) :
    ¬ Solvable bs ↔ Refutable bs :=
  ⟨refutable_of_not_solvable bs hI, Refutable.not_solvable⟩

end KLM

end Petri

end HTN
