import HtnComplexity.AcVerify.VerExec2
import HtnComplexity.AcVerify.VerEntry
import HtnComplexity.AcVerify.Sound
/-!
# Soundness of the verifier

`HTN.Syn.AcVer.solvable_of_acV`: if the verifier accepts a certificate for the instance code
`instSer q` and the advice `advOf d`, the described problem is solvable.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

variable {d : DomDesc} {q : InstDesc}

/-- **Every record accepted by the record test is the record of a step.** -/
theorem recs_of_recsB (e : CE) (h : recsB (instSer q) (advOf d) e.enc = true) :
    ∃ p : List PStep, e.recs = p.map (recOf d q) := by
  unfold recsB at h
  rw [enc_eq_recs e] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hroot⟩, hall⟩ := h
  rw [entAll_iff] at hall
  refine exists_map_of_forall fun w hw => ?_
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hw
  have := hall l₁ w l₂ hsplit
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, entriesEnc_eq_nil] at this
  rcases this.1.1 with (h0 | hm) | ⟨-, hdm⟩
  · subst h0
    rw [hsplit, List.nil_append, nextEnt_blist, rootRecB_iff d q] at hroot
    obtain ⟨i, -, hi⟩ := hroot
    simp only [List.cons.injEq, true_and] at hi
    exact ⟨(0, i), (bstr_parse (r := []) (s := []) (by simpa using hi)).1.symm⟩
  · rw [advOf_eq, occB_iff, mem_mstepT] at hm
    obtain ⟨k, hk, j, -, rfl⟩ := hm
    exact ⟨(k, j), recOf_mem_of_mIdx hk⟩
  · rw [tD_advOf, List.append_assoc, List.append_assoc, occB_iff, mem_dummyT] at hdm
    obtain ⟨k, hk, -, rfl⟩ := hdm
    exact ⟨(k, 0), recOf_mem_of_mIdx hk⟩

theorem isChain_of_entryOK {u : Entry} (h : EntryOK d q u) : u.1.IsChain (Link d q) := by
  unfold EntryOK at h
  split_ifs at h
  · obtain ⟨p, y, -, -, -, hc, -⟩ := h; exact hc
  · exact h.1.2.1

theorem first_of_entryOK {u : Entry} (h : EntryOK d q u) : ∃ i s, u.1 = (0, i) :: s := by
  unfold EntryOK at h
  split_ifs at h
  · obtain ⟨p, y, hp, -, ⟨⟨i, s, hs⟩, -⟩, -⟩ := h
    exact ⟨i, s ++ [y], by rw [hp, hs]; rfl⟩
  · exact h.1.1

/-- The steps of an action leaf are steps of their networks, and the later ones are steps of
listed methods. -/
theorem leafSteps_of_entryOK {p : List PStep} (h : EntryOK d q (p, false)) : LeafSteps d q p := by
  have hc := isChain_of_entryOK h
  obtain ⟨i, s, hs⟩ := first_of_entryOK h
  unfold EntryOK at h
  simp only [Bool.false_eq_true, if_false] at h
  intro x hx
  refine ⟨h.1.2.2 x hx, fun hx0 => ?_⟩
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hx
  rcases l₁.eq_nil_or_concat with rfl | ⟨l₁', y, rfl⟩
  · simp only at hs
    rw [hsplit] at hs
    simp only [List.nil_append, List.cons.injEq] at hs
    exact absurd (by rw [hs.1]) hx0
  · exact mIdx_of_link (splits_of_isChain hc l₁' y x l₂ (by simp [hsplit]))

/-- **Soundness of the verifier**: an accepted certificate yields a path witness. -/
theorem pathOK_of_acV {w : List Bool} (h : acV [instSer q, advOf d, w] = true) :
    ∃ W, PathOK d q W := by
  unfold acV at h
  simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hbl, hall⟩, hroots⟩, hpairs⟩, hexec⟩ := h
  obtain ⟨l, rfl⟩ := blistB_iff.1 hbl
  rw [show blist l = blist l ++ [] by simp, entAll_mem] at hall
  simp only [cont_entry, Bool.and_eq_true] at hall
  obtain ⟨cs, hcs⟩ := exists_ces (w := blist l) hbl fun c ⟨l', z, he, hc⟩ => by
    obtain ⟨rfl, -⟩ := blist_parse (r := []) (s := z) (by simpa using he)
    exact (hall c hc).1.1
  rw [List.append_nil] at hall
  obtain rfl : l = cs.map CE.enc := blist_parse (r := []) (s := []) (by simpa using hcs) |>.1
  have hrecs : ∀ e ∈ cs, recsB (instSer q) (advOf d) e.enc = true :=
    fun e he => (hall _ (List.mem_map_of_mem he)).1.2
  have hchild : ∀ e ∈ cs, childB (advOf d) (blist (cs.map CE.enc)) e.enc = true :=
    fun e he => (hall _ (List.mem_map_of_mem he)).2
  have hst : ∀ e ∈ cs, e.recs = (stepsOf d q e).map (recOf d q) := fun e he => by
    obtain ⟨p, hp⟩ := recs_of_recsB e (hrecs e he)
    rw [stepsOf_eq hp]; exact hp
  have hent : ∀ e ∈ cs, EntryOK0 d q (stepsOf d q e, e.f) := fun e he => by
    have := (recsB_iff d q e _ (hst e he)).1 (hrecs e he)
    exact (recs_iff_entryOK0 _ _).1 this
  refine ⟨cs.map fun e => (stepsOf d q e, e.f), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · -- entries
    intro u hu
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
    exact (hent e he).1
  · -- pairs
    rw [show blist (cs.map CE.enc) = blist (cs.map CE.enc) ++ [] by simp] at hpairs
    unfold pairsB at hpairs
    rw [entAll_iff, forall_split_map CE.enc cs (fun l₁ w l₂ => _ = true)] at hpairs
    rw [pairwise_iff_splits]
    intro l₁ a l₂ hsplit b hb
    obtain ⟨m₁, m₂, mm, hm₁, hm₂⟩ := List.map_eq_append_iff.1 hsplit
    obtain ⟨eu, m₂', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hm₂
    obtain ⟨ev, hev, rfl⟩ := List.mem_map.1 hb
    have h2 := hpairs m₁ eu m₂' mm
    rw [entAll_iff, forall_split_map CE.enc m₂' (fun l₁ w l₂ => _ = true)] at h2
    obtain ⟨n₁, n₂, hn⟩ := List.append_of_mem hev
    have h3 := h2 n₁ ev n₂ hn
    rw [cont_entry, cont_entry] at h3
    have heu : eu ∈ cs := by rw [mm]; simp
    have hevm : ev ∈ cs := by rw [mm]; simp [hev]
    refine (pairB_iff (d := d) (q := q) (stepsOf d q eu) (stepsOf d q ev) _ _ _ _
      (enc_eq_recs eu |>.trans (by rw [hst eu heu])) (enc_eq_recs ev |>.trans (by rw [hst ev hevm]))
      eu.f ev.f (CE.flagOf_enc _) (CE.flagOf_enc _) ?_).1 h3
    intro hfu hfv
    have h1 := (hent eu heu).1
    have h2 := (hent ev hevm).1
    rw [hfu] at h1; rw [hfv] at h2
    exact ⟨leafSteps_of_entryOK h1, leafSteps_of_entryOK h2⟩
  · -- roots
    exact (rootsB_iff cs hst).1 hroots
  · -- children
    intro u hu P x y s hsplit j hj
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
    have hc := isChain_of_entryOK (hent e he).1
    have hlink := splits_of_isChain hc P x y s hsplit
    have hk := mIdx_of_link hlink
    rw [netOf_of_ne (mIdx_ne_zero hk)] at hj
    have := (childB_iff cs hst e _ (hst e he)).1 (hchild e he) (P ++ [x]) y s
      (by simpa using hsplit) (by simp) j hj hk
    obtain ⟨e', he', s', hs'⟩ := this
    exact ⟨_, List.mem_map_of_mem he', s', by simpa using hs'⟩
  · -- execution
    refine execOK_of_execB cs (fun e he hr => ?_) hexec
    have hE := (hent e he).1
    obtain ⟨i, s, hs⟩ := first_of_entryOK hE
    obtain ⟨p', x, hpx⟩ : ∃ p' x, stepsOf d q e = p' ++ [x] := by
      rcases (stepsOf d q e).eq_nil_or_concat with h0 | ⟨p', x, h1⟩
      · simp only at hs; rw [h0] at hs; simp at hs
      · exact ⟨p', x, by simpa using h1⟩
    have hlast : (stepsOf d q e).getLast? = some x := by rw [hpx]; simp
    refine (rowB_iff e (stepsOf d q e) x (actOf d q e) (hst e he) hlast (fun hf => ?_)).1 hr
    unfold EntryOK at hE
    simp only [hf, Bool.false_eq_true, if_false] at hE
    obtain ⟨a, ha⟩ := hE.2
    have hl : lastLabel d q (stepsOf d q e) = stepLabel d q x := by
      simp [lastLabel, hlast]
    rw [hl] at ha
    simp [actOf, leafAct, hl, ha]

/-- **Soundness of the verifier.** -/
theorem solvable_of_acV {w : List Bool} (h : acV [instSer q, advOf d, w] = true) : Solvable d q :=
  solvable_iff_exists_pathOK.2 (pathOK_of_acV h)

end AcVer

end Syn

end HTN
