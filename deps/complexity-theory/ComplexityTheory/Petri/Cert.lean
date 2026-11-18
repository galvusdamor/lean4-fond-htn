import ComplexityTheory.Petri.CAltsD
/-!
# Certificates of non-solvability, checked by list-bounded conditions

A certificate is a list of nodes `(gp, rule)`.  A rule names a decomposition step and its data
(`CRule = tag × position × R × edge × coordinate × bound × node list`).  A node is valid with
respect to the list `pref` of the nodes before it (`nodeOK`) if the side conditions of its step
hold (`localOK`, with only list-bounded quantifiers and the bounded-search test `feasB`) and each
of its children (`children`) is the problem of some node of `pref`.

* `refutable_of_valid` — every problem of a valid certificate is refutable (soundness);
* `exists_valid_of_refutable` — every refutable problem is the problem of a node of some valid
  certificate (completeness);
* `refutable_iff_cert`.
-/

namespace HTN

namespace Petri

namespace KLM

open Finset Euler Comp Classical

noncomputable section

variable {d : ℕ}

/-! ### Rules and nodes -/

/-- A rule: tag, position of the block, node set, edge, coordinate, bound, node list. -/
abbrev CRule : Type := ℕ × ℕ × List ℕ × CE × ℕ × ℕ × List (ℕ × CW)

/-- A certificate node. -/
abbrev CNode : Type := List CB × CRule

def rTag (r : CRule) : ℕ := r.1
def rPos (r : CRule) : ℕ := r.2.1
def rR (r : CRule) : List ℕ := r.2.2.1
def rCe (r : CRule) : CE := r.2.2.2.1
def rJ (r : CRule) : ℕ := r.2.2.2.2.1
def rB (r : CRule) : ℕ := r.2.2.2.2.2.1
def rNs (r : CRule) : List (ℕ × CW) := r.2.2.2.2.2.2

/-- The block a rule acts on. -/
def rBlk (gp : List CB) (r : CRule) : CB := gp.getD (rPos r) default

/-- The concrete alternatives of a rule. -/
def ralts (d : ℕ) (gp : List CB) (r : CRule) : List (List CB) :=
  if rTag r = 1 then cprune (rBlk gp r) (rR r)
  else if rTag r = 2 then csplit (rBlk gp r) (rR r)
  else if rTag r = 3 then cedgeAlts d (rBlk gp r) (rCe r) (rB r)
  else if rTag r = 4 then cinpAlts d (rBlk gp r) (rJ r) (rB r)
  else if rTag r = 5 then coutAlts d (rBlk gp r) (rJ r) (rB r)
  else if rTag r = 6 then cdAlts d (rBlk gp r) (rNs r)
  else if rTag r = 7 then cdAltsB d (rBlk gp r) (rNs r)
  else []

/-- The children of a node. -/
def children (d : ℕ) (gp : List CB) (r : CRule) : List (List CB) :=
  (ralts d gp r).map fun A => gp.take (rPos r) ++ A ++ gp.drop (rPos r + 1)

/-- The bound test of block `i` for a list of terms. -/
def bndEq (d : ℕ) (gp : List CB) (lin : List (ℕ × ℤ)) (B : ℕ) : List TEq :=
  sysFrom d 0 gp ++ [(lin ++ [(totW (d := d) gp, -1)], (B : ℤ) + 1)]

/-- **The side conditions of a rule.** -/
def localOK (d : ℕ) (gp : List CB) (r : CRule) : Prop :=
  (rTag r = 0 ∧ feasB (sysFrom d 0 gp) = false) ∨
  (rPos r < gp.length ∧
    ((rTag r = 1 ∧ cEntry (cComp (rBlk gp r)) ∈ rR r ∧
        ∀ e ∈ cEdges (cComp (rBlk gp r)), e.1 ∈ rR r → e.2.2 ∈ rR r) ∨
     (rTag r = 2 ∧ cEntry (cComp (rBlk gp r)) ∈ rR r ∧
        ∀ e ∈ cEdges (cComp (rBlk gp r)), e.2.2 ∈ rR r → e.1 ∈ rR r) ∨
     (rTag r = 3 ∧ rCe r ∈ cEdges (cComp (rBlk gp r)) ∧
        feasB (bndEq d gp (edgeLin (d := d) gp (rPos r) (rCe r)) (rB r)) = false) ∨
     (rTag r = 4 ∧ rJ r < d ∧ (cInp (rBlk gp r)).getD (rJ r) none = none ∧
        feasB (bndEq d gp [(offs (d := d) gp (rPos r) + rJ r, 1)] (rB r)) = false) ∨
     (rTag r = 5 ∧ rJ r < d ∧ (cOut (rBlk gp r)).getD (rJ r) none = none ∧
        feasB (bndEq d gp [(offs (d := d) gp (rPos r) + d + rJ r, 1)] (rB r)) = false) ∨
     (rTag r = 6 ∧ cEntryOK d (rBlk gp r) ∧ cDCert d (rBlk gp r) (rNs r)) ∨
     (rTag r = 7 ∧ cExitOK d (rBlk gp r) ∧ cDCert d (crevB (rBlk gp r)) (rNs r))))

/-- A node is valid with respect to the nodes before it. -/
def nodeOK (d : ℕ) (pref : List CNode) (nd : CNode) : Prop :=
  localOK d nd.1 nd.2 ∧ ∀ c ∈ children d nd.1 nd.2, ∃ q ∈ pref, q.1 = c

/-- **A valid certificate.** -/
def Valid (d : ℕ) (cert : List CNode) : Prop :=
  ∀ n ∈ List.range cert.length, nodeOK d (cert.take n) (cert.getD n default)

/-- **A certificate for the problem `gp`.** -/
def Accepts (d : ℕ) (gp : List CB) (cert : List CNode) : Prop :=
  Valid d cert ∧ ∃ q ∈ cert, q.1 = gp

/-! ### Validity lemmas -/

theorem nodeOK_mono {pref pref' : List CNode} (h : ∀ q ∈ pref, q ∈ pref') {nd : CNode}
    (hn : nodeOK d pref nd) : nodeOK d pref' nd :=
  ⟨hn.1, fun c hc => by
    obtain ⟨q, hq, rfl⟩ := hn.2 c hc
    exact ⟨q, h q hq, rfl⟩⟩

theorem valid_nil : Valid d [] := fun n hn => by simp at hn

theorem valid_append {c₁ c₂ : List CNode} (h₁ : Valid d c₁) (h₂ : Valid d c₂) :
    Valid d (c₁ ++ c₂) := by
  intro n hn
  rw [List.mem_range, List.length_append] at hn
  by_cases hlt : n < c₁.length
  · rw [List.take_append_of_le_length hlt.le, List.getD_append _ _ _ _ hlt]
    exact h₁ n (List.mem_range.2 hlt)
  · push_neg at hlt
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlt
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    exact nodeOK_mono (fun q hq => List.mem_append_right _ hq) (h₂ m (List.mem_range.2 (by omega)))

theorem valid_snoc {c : List CNode} {nd : CNode} (h : Valid d c) (hn : nodeOK d c nd) :
    Valid d (c ++ [nd]) := by
  intro n hn'
  rw [List.mem_range, List.length_append, List.length_singleton] at hn'
  by_cases hlt : n < c.length
  · rw [List.take_append_of_le_length hlt.le, List.getD_append _ _ _ _ hlt]
    exact h n (List.mem_range.2 hlt)
  · have : n = c.length := by omega
    subst this
    rw [List.take_left' rfl, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    exact hn

/-! ### Soundness -/

theorem split_gp (gp : List CB) {i : ℕ} (hi : i < gp.length) :
    gp.map (decB d) = (gp.take i).map (decB d) ++ decB d (gp.getD i default) ::
      (gp.drop (i + 1)).map (decB d) := by
  rw [List.getD_eq_getElem _ _ hi]
  have h1 : gp = gp.take i ++ gp[i] :: gp.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  exact (congrArg (List.map (decB d)) h1).trans (by simp only [List.map_append, List.map_cons])

theorem length_take_map (gp : List CB) {i : ℕ} (hi : i < gp.length) :
    ((gp.take i).map (decB d)).length = i := by simp; omega

/-- Refutability from the refutability of the decoded children. -/
theorem alts_refutable {gp : List CB} {r : CRule} {As : List (List (Block (Fin d)))}
    (hAs : As = (ralts d gp r).map (List.map (decB d)))
    (hch : ∀ c ∈ children d gp r, Refutable (c.map (decB d))) :
    ∀ A ∈ As, Refutable ((gp.take (rPos r)).map (decB d) ++ A ++ (gp.drop (rPos r + 1)).map (decB d)) := by
  intro A hA
  rw [hAs] at hA
  obtain ⟨cA, hcA, rfl⟩ := List.mem_map.1 hA
  have := hch _ (List.mem_map_of_mem (f := fun A => gp.take (rPos r) ++ A ++ gp.drop (rPos r + 1)) hcA)
  simpa using this

/-- One node: its side conditions and refutable children make its problem refutable. -/
theorem refutable_of_node {gp : List CB} {r : CRule} (hl : localOK d gp r)
    (hch : ∀ c ∈ children d gp r, Refutable (c.map (decB d))) : Refutable (gp.map (decB d)) := by
  rcases hl with ⟨-, hf⟩ | ⟨hpos, hl⟩
  · refine Refutable.noChar ?_
    rw [noChar_iff]
    rintro ⟨x, hx⟩
    have := (feasB_iff _).2 ⟨x, hx⟩
    rw [hf] at this
    exact Bool.noConfusion this
  have hsp := split_gp (d := d) gp hpos
  have hlen := length_take_map (d := d) gp hpos
  set b := gp.getD (rPos r) default with hb
  have hbb : rBlk gp r = b := rfl
  rw [hsp]
  rcases hl with ⟨ht, hR, hcl⟩ | ⟨ht, hR, hcl⟩ | ⟨ht, hce, hf⟩ | ⟨ht, hj, hinp, hf⟩ |
    ⟨ht, hj, hout, hf⟩ | ⟨ht, hE, hD⟩ | ⟨ht, hE, hD⟩
  · refine Refutable.prune (rR r) hR (fun e he h1 => ?_) (alts_refutable ?_ hch)
    · obtain ⟨ce, hce, rfl⟩ := List.mem_map.1 he
      exact hcl ce hce h1
    · simp only [ralts, ht, if_true, hbb]; exact prune_dec b (rR r)
  · refine Refutable.split (rR r) hR (fun e he h1 => ?_) (alts_refutable ?_ hch)
    · obtain ⟨ce, hce, rfl⟩ := List.mem_map.1 he
      exact hcl ce hce h1
    · simp only [ralts, ht, hbb]; exact split_dec b (rR r)
  · refine Refutable.edge (decE d (rCe r)) (rB r) (List.mem_map_of_mem hce) ?_ (alts_refutable ?_ hch)
    · rw [← hsp, hlen]
      have := (edgeBound_iff gp (rPos r) hpos (rCe r) (rB r)).2 (by
        rw [← feasB_iff]; unfold bndEq at hf; rw [hf]; simp)
      rw [hb, List.getD_eq_getElem _ _ hpos]
      exact this
    · simp only [ralts, ht, hbb]; exact edge_dec b (rCe r) (rB r)
  · have hj' : (decB d b).inp ⟨rJ r, hj⟩ = ⊤ := by
      simp only [decB_inp, decW_apply, decO_eq_top]; exact hinp
    refine Refutable.inp ⟨rJ r, hj⟩ (rB r) hj' ?_ (alts_refutable ?_ hch)
    · rw [← hsp, hlen]
      exact (inpBound_iff gp (rPos r) hpos ⟨rJ r, hj⟩ (rB r)).2 (by
        rw [← feasB_iff]; unfold bndEq at hf; rw [hf]; simp)
    · simp only [ralts, ht, hbb]; exact inp_dec b ⟨rJ r, hj⟩ (rB r)
  · have hj' : (decB d b).out ⟨rJ r, hj⟩ = ⊤ := by
      simp only [decB_out, decW_apply, decO_eq_top]; exact hout
    refine Refutable.out ⟨rJ r, hj⟩ (rB r) hj' ?_ (alts_refutable ?_ hch)
    · rw [← hsp, hlen]
      exact (outBound_iff gp (rPos r) hpos ⟨rJ r, hj⟩ (rB r)).2 (by
        rw [← feasB_iff]; unfold bndEq at hf; rw [hf]; simp)
    · simp only [ralts, ht, hbb]; exact out_dec b ⟨rJ r, hj⟩ (rB r)
  · refine Refutable.dF (decNs d (rNs r)) ((cEntryOK_iff b).1 hE) ((cDCert_iff b _).1 hD)
      (alts_refutable ?_ hch)
    simp only [ralts, ht, hbb]; exact d_dec b (rNs r)
  · refine Refutable.dB (decNs d (rNs r)) ((cExitOK_iff b).1 hE) ?_ (alts_refutable ?_ hch)
    · rw [← decB_crevB]; exact (cDCert_iff _ _).1 hD
    · simp only [ralts, ht, hbb]; exact dB_dec b (rNs r)

/-- **Soundness of certificates.** -/
theorem refutable_of_valid {cert : List CNode} (h : Valid d cert) :
    ∀ q ∈ cert, Refutable (q.1.map (decB d)) := by
  suffices H : ∀ n, n < cert.length → Refutable ((cert.getD n default).1.map (decB d)) by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hq
    have := H n hn
    rwa [List.getD_eq_getElem _ _ hn] at this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨hl, hch⟩ := h n (List.mem_range.2 hn)
    refine refutable_of_node hl fun c hc => ?_
    obtain ⟨q, hq, rfl⟩ := hch c hc
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hq
    rw [List.length_take] at hm
    have := ih m (by omega) (by omega)
    rwa [List.getElem_take, ← List.getD_eq_getElem _ default]

end

end KLM

end Petri

end HTN
