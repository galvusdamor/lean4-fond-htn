import ComplexityTheory.Petri.Cert
/-!
# Completeness of certificates

`exists_cert_of_refutable`: every refutable decoded problem has a valid certificate; together with
soundness, `refutable_iff_cert`.
-/

namespace HTN

namespace Petri

namespace KLM

open Finset Euler Comp Classical

noncomputable section

variable {d : ℕ}

/-! ### Encoding `ω`-vectors -/

/-- Encoding an extended natural number. -/
def toOpt (x : ℕ∞) : Option ℕ := if x = ⊤ then none else some x.toNat

theorem decO_toOpt (x : ℕ∞) : decO (toOpt x) = x := by
  unfold toOpt
  split_ifs with h
  · simp [decO, h]
  · simp only [decO]; exact ENat.coe_toNat h

/-- Encoding an `ω`-vector. -/
def encW (d : ℕ) (μ : Fin d → ℕ∞) : CW := List.ofFn fun j => toOpt (μ j)

theorem decW_encW (μ : Fin d → ℕ∞) : decW d (encW d μ) = μ := by
  funext j
  rw [decW_apply, encW, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  exact decO_toOpt _

/-- Encoding a node list. -/
def encNs (d : ℕ) (Ns : List (ℕ × (Fin d → ℕ∞))) : List (ℕ × CW) :=
  Ns.map fun p => (p.1, encW d p.2)

theorem decNs_encNs (Ns : List (ℕ × (Fin d → ℕ∞))) : decNs d (encNs d Ns) = Ns := by
  simp only [decNs, encNs, List.map_map, Function.comp_def, decW_encW]
  exact List.map_id' _ ▸ rfl

/-! ### Splitting the decoded problem -/

theorem map_eq_append_cons {gp : List CB} {pre post : List (Block (Fin d))} {b : Block (Fin d)}
    (h : gp.map (decB d) = pre ++ b :: post) :
    pre.length < gp.length ∧ pre = (gp.take pre.length).map (decB d) ∧
      b = decB d (gp.getD pre.length default) ∧ post = (gp.drop (pre.length + 1)).map (decB d) := by
  obtain ⟨l₁, l₂, rfl, rfl, h2⟩ := List.map_eq_append_iff.1 h
  obtain ⟨c, l₃, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 h2
  simp only [List.length_map]
  refine ⟨by simp, by rw [List.take_left' rfl], ?_, ?_⟩
  · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
  · rw [List.drop_append]
    simp

/-! ### Assembling certificates -/

theorem combine : ∀ cs : List (List CB), (∀ c ∈ cs, ∃ cert, Accepts d c cert) →
    ∃ cert, Valid d cert ∧ ∀ c ∈ cs, ∃ q ∈ cert, q.1 = c
  | [], _ => ⟨[], valid_nil, fun c hc => by simp at hc⟩
  | c :: cs, h => by
    obtain ⟨cert₁, hv₁, q, hq, hqc⟩ := h c (by simp)
    obtain ⟨cert₂, hv₂, h₂⟩ := combine cs fun c' hc' => h c' (by simp [hc'])
    refine ⟨cert₁ ++ cert₂, valid_append hv₁ hv₂, fun c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact ⟨q, List.mem_append_left _ hq, hqc⟩
    · obtain ⟨q', hq', h'⟩ := h₂ c' hc'
      exact ⟨q', List.mem_append_right _ hq', h'⟩

theorem accepts_of_node {gp : List CB} {r : CRule} (hl : localOK d gp r)
    (hch : ∀ c ∈ children d gp r, ∃ cert, Accepts d c cert) : ∃ cert, Accepts d gp cert := by
  obtain ⟨big, hv, hbig⟩ := combine _ hch
  exact ⟨big ++ [(gp, r)], valid_snoc hv ⟨hl, hbig⟩, (gp, r), by simp, rfl⟩

/-- The children of a node, through the abstract alternatives. -/
theorem children_of_alts {gp : List CB} {r : CRule} {As : List (List (Block (Fin d)))}
    (hAs : As = (ralts d gp r).map (List.map (decB d)))
    (ih : ∀ A ∈ As, ∀ gp' : List CB,
      (gp.take (rPos r)).map (decB d) ++ A ++ (gp.drop (rPos r + 1)).map (decB d) = gp'.map (decB d) →
        ∃ cert, Accepts d gp' cert) :
    ∀ c ∈ children d gp r, ∃ cert, Accepts d c cert := by
  intro c hc
  obtain ⟨cA, hcA, rfl⟩ := List.mem_map.1 hc
  exact ih (cA.map (decB d)) (by rw [hAs]; exact List.mem_map_of_mem hcA) _ (by simp)

/-- A rule with given tag and data. -/
def mkRule (tag pos : ℕ) (R : List ℕ := []) (ce : CE := (0, [], 0)) (j B : ℕ := 0)
    (Ns : List (ℕ × CW) := []) : CRule := (tag, pos, R, ce, j, B, Ns)

/-- **Completeness of certificates.** -/
theorem exists_cert_of_refutable {gp : List CB} (h : Refutable (gp.map (decB d))) :
    ∃ cert, Accepts d gp cert := by
  generalize hbs : gp.map (decB d) = bs at h
  induction h generalizing gp with
  | noChar hn =>
    subst hbs
    refine accepts_of_node (r := mkRule 0 0) (Or.inl ⟨rfl, ?_⟩) (fun c hc => ?_)
    · rw [noChar_iff, ← feasB_iff] at hn
      simpa using hn
    · simp [children, ralts, mkRule, rTag] at hc
  | @prune pre post b R hR hcl _ ih =>
    obtain ⟨hi, hpre, hb, hpost⟩ := map_eq_append_cons hbs
    let r := mkRule 1 pre.length R
    refine accepts_of_node (r := r) (Or.inr ⟨hi, Or.inl ⟨rfl, ?_, fun e he h1 => ?_⟩⟩)
      (children_of_alts (As := pruneAlts b (· ∈ R)) ?_ ?_)
    · have : b.comp.entry ∈ R := hR
      rwa [hb] at this
    · have := hcl (decE d e) (by rw [hb]; exact List.mem_map_of_mem he) h1
      exact this
    · simp only [ralts, r, mkRule, rTag, if_true, hb]; exact prune_dec _ R
    · intro A hA gp' hgp'
      exact ih A hA (by rw [← hgp']; simp only [r, mkRule, rPos]; rw [← hpre, ← hpost])
  | @split pre post b S hS hcl _ ih =>
    obtain ⟨hi, hpre, hb, hpost⟩ := map_eq_append_cons hbs
    let r := mkRule 2 pre.length S
    refine accepts_of_node (r := r) (Or.inr ⟨hi, Or.inr (Or.inl ⟨rfl, ?_, fun e he h1 => ?_⟩)⟩)
      (children_of_alts (As := splitAlts b (· ∈ S)) ?_ ?_)
    · have : b.comp.entry ∈ S := hS
      rwa [hb] at this
    · have := hcl (decE d e) (by rw [hb]; exact List.mem_map_of_mem he) h1
      exact this
    · simp only [ralts, r, mkRule, rTag, hb]; exact split_dec _ S
    · intro A hA gp' hgp'
      exact ih A hA (by rw [← hgp']; simp only [r, mkRule, rPos]; rw [← hpre, ← hpost])
  | @edge pre post b e₀ B he₀ hB _ ih =>
    obtain ⟨hi, hpre, hb, hpost⟩ := map_eq_append_cons hbs
    subst hb
    obtain ⟨ce, hce, rfl⟩ := List.mem_map.1 he₀
    let r := mkRule 3 pre.length [] ce 0 B
    refine accepts_of_node (r := r)
      (Or.inr ⟨hi, Or.inr (Or.inr (Or.inl ⟨rfl, hce, ?_⟩))⟩)
      (children_of_alts ?_ fun A hA gp' hgp' => ih A hA ?_)
    · have hB' := hB
      rw [← hbs] at hB'
      rw [List.getD_eq_getElem _ _ hi] at hB'
      have := (edgeBound_iff gp pre.length hi ce B).1 hB'
      rw [← feasB_iff] at this
      simpa [bndEq, r, mkRule, rPos, rCe, rB] using this
    · simp only [ralts, r, mkRule, rTag]; exact edge_dec _ ce B
    · rw [← hgp']; simp only [r, mkRule, rPos]; rw [← hpre, ← hpost]
  | @inp pre post b j B hj hB _ ih =>
    obtain ⟨hi, hpre, hb, hpost⟩ := map_eq_append_cons hbs
    subst hb
    let r := mkRule 4 pre.length [] (0, [], 0) j B
    refine accepts_of_node (r := r)
      (Or.inr ⟨hi, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, j.2, ?_, ?_⟩)))⟩)
      (children_of_alts ?_ fun A hA gp' hgp' => ih A hA ?_)
    · have := hj
      simp only [decB_inp, decW_apply, decO_eq_top] at this
      exact this
    · have hB' := hB
      rw [← hbs] at hB'
      have := (inpBound_iff gp pre.length hi j B).1 hB'
      rw [← feasB_iff] at this
      simpa [bndEq, r, mkRule, rPos, rJ, rB] using this
    · simp only [ralts, r, mkRule, rTag]; exact inp_dec _ j B
    · rw [← hgp']; simp only [r, mkRule, rPos]; rw [← hpre, ← hpost]
  | @out pre post b j B hj hB _ ih =>
    obtain ⟨hi, hpre, hb, hpost⟩ := map_eq_append_cons hbs
    subst hb
    let r := mkRule 5 pre.length [] (0, [], 0) j B
    refine accepts_of_node (r := r)
      (Or.inr ⟨hi, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, j.2, ?_, ?_⟩))))⟩)
      (children_of_alts ?_ fun A hA gp' hgp' => ih A hA ?_)
    · have := hj
      simp only [decB_out, decW_apply, decO_eq_top] at this
      exact this
    · have hB' := hB
      rw [← hbs] at hB'
      have := (outBound_iff gp pre.length hi j B).1 hB'
      rw [← feasB_iff] at this
      simpa [bndEq, r, mkRule, rPos, rJ, rB] using this
    · simp only [ralts, r, mkRule, rTag]; exact out_dec _ j B
    · rw [← hgp']; simp only [r, mkRule, rPos]; rw [← hpre, ← hpost]
  | @dF pre post b Ns hin hD _ ih =>
    obtain ⟨hi, hpre, hb, hpost⟩ := map_eq_append_cons hbs
    subst hb
    let r := mkRule 6 pre.length [] (0, [], 0) 0 0 (encNs d Ns)
    refine accepts_of_node (r := r)
      (Or.inr ⟨hi, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)))))⟩)
      (children_of_alts (As := dAlts (decB d (gp.getD pre.length default)) Ns) ?_ ?_)
    · exact (cEntryOK_iff _).2 hin
    · rw [cDCert_iff]
      show DCert _ (decNs d (encNs d Ns))
      rw [decNs_encNs]; exact hD
    · simp only [ralts, r, mkRule, rTag]
      have := d_dec (d := d) (gp.getD pre.length default) (encNs d Ns)
      rwa [decNs_encNs] at this
    · intro A hA gp' hgp'
      exact ih A hA (by rw [← hgp']; simp only [r, mkRule, rPos]; rw [← hpre, ← hpost])
  | @dB pre post b Ns hout hD _ ih =>
    obtain ⟨hi, hpre, hb, hpost⟩ := map_eq_append_cons hbs
    subst hb
    let r := mkRule 7 pre.length [] (0, [], 0) 0 0 (encNs d Ns)
    refine accepts_of_node (r := r)
      (Or.inr ⟨hi, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)))))⟩)
      (children_of_alts (As := dAltsB (decB d (gp.getD pre.length default)) Ns) ?_ ?_)
    · exact (cExitOK_iff _).2 hout
    · rw [cDCert_iff, decB_crevB]
      show DCert _ (decNs d (encNs d Ns))
      rw [decNs_encNs]; exact hD
    · simp only [ralts, r, mkRule, rTag]
      have := dB_dec (d := d) (gp.getD pre.length default) (encNs d Ns)
      rwa [decNs_encNs] at this
    · intro A hA gp' hgp'
      exact ih A hA (by rw [← hgp']; simp only [r, mkRule, rPos]; rw [← hpre, ← hpost])

/-- **Refutability of a decoded problem is the existence of a certificate.** -/
theorem refutable_iff_cert (gp : List CB) :
    Refutable (gp.map (decB d)) ↔ ∃ cert, Accepts d gp cert := by
  refine ⟨exists_cert_of_refutable, ?_⟩
  rintro ⟨cert, hv, q, hq, rfl⟩
  exact refutable_of_valid hv q hq

end

end KLM

end Petri

end HTN
