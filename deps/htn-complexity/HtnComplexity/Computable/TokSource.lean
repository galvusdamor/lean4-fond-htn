import HtnComplexity.Computable.TokDom
/-!
# The blocks of a described regular method

`HTN.Method.HasBlock` (`HtnComplexity/Regular/RegularWeakNormalForm.lean`) says that a method
decomposes its compound task into a *block* of primitive tasks — one linearization of its
primitive part — followed by at most one compound task.  For a **described** method this file
identifies the blocks concretely: they are the enumerations `xs` of the primitive identifiers
of the description that respect its ordering (`HTN.Syn.TnDesc.PrimLin`), and the block is the
sequence of actions labelling `xs`.

`HTN.Syn.TnDesc.hasBlock_iff` is the source-side interface of the token-gadget compilation.
-/

namespace HTN

namespace Syn

namespace TnDesc

/-- **An enumeration of the primitive part of a described network**: a repetition-free list of
exactly its primitive identifiers, in an order consistent with the described ordering. -/
def PrimLin (t : TnDesc) (xs : List ℕ) : Prop :=
  xs.Nodup ∧ (∀ x, x ∈ xs ↔ x ∈ primIds t) ∧
    xs.Pairwise (fun a b => ¬ t.toTaskNetwork.ord b a)

variable {t : TnDesc}

theorem mem_T_iff {x : ℕ} : x ∈ t.toTaskNetwork.T ↔ x ∈ t.ids := by
  simp

theorem isAbstractId_iff {x : ℕ} :
    t.toTaskNetwork.IsAbstractId x ↔ ∃ c, t.label x = Sum.inr c := Iff.rfl

theorem not_isAbstractId_of_mem_primIds {x : ℕ} (h : x ∈ primIds t) :
    ¬ t.toTaskNetwork.IsAbstractId x := by
  obtain ⟨-, a, ha⟩ := mem_primIds.1 h
  rintro ⟨c, hc⟩
  rw [show t.toTaskNetwork.α x = t.label x from rfl, ha] at hc
  exact absurd hc (by simp)

theorem mem_primIds_of_not_abstract {x : ℕ} (hx : x ∈ t.ids)
    (h : ¬ t.toTaskNetwork.IsAbstractId x) : x ∈ primIds t := by
  refine mem_primIds.2 ⟨hx, ?_⟩
  rcases hcase : t.label x with a | c
  · exact ⟨a, rfl⟩
  · exact absurd ⟨c, hcase⟩ h

/-- If the described network has a compound task, it is the unique abstract identifier and its
name is `nextName`. -/
theorem exists_unique_compound (hreg : t.toTaskNetwork.IsRegular) (h : hasNextB t = true) :
    ∃ z ∈ t.ids, t.label z = Sum.inr (nextName t) ∧
      ∀ y ∈ t.ids, t.toTaskNetwork.IsAbstractId y → y = z := by
  obtain ⟨z, hz, hlab⟩ := exists_compound h
  refine ⟨z, hz, hlab, ?_⟩
  intro y hy hay
  exact hreg.1 y (mem_T_iff.2 hy) z (mem_T_iff.2 hz) hay ⟨_, hlab⟩

theorem nextName_eq (hreg : t.toTaskNetwork.IsRegular) {z c : ℕ} (hz : z ∈ t.ids)
    (hlab : t.label z = Sum.inr c) : hasNextB t = true ∧ nextName t = c := by
  have hmem : c ∈ t.compoundNames := mem_compoundNames.2 ⟨z, hz, hlab⟩
  have hne : t.compoundNames ≠ [] := by
    intro hcon
    rw [hcon] at hmem
    simp at hmem
  have h : hasNextB t = true := by
    simp [hasNextB, hne]
  refine ⟨h, ?_⟩
  obtain ⟨z', hz', hlab'⟩ := exists_compound h
  have : z' = z := hreg.1 z' (mem_T_iff.2 hz') z (mem_T_iff.2 hz) ⟨_, hlab'⟩ ⟨_, hlab⟩
  rw [this, hlab] at hlab'
  simpa using hlab'.symm

/-- **The blocks of a described regular method**: they are exactly the enumerations of its
primitive part. -/
theorem hasBlock_iff (hreg : t.toTaskNetwork.IsRegular) (c : ℕ) {os : List ℕ}
    {next : Option ℕ} :
    (MethodDesc.toMethod (c, t)).HasBlock os next ↔
      ∃ xs : List ℕ, PrimLin t xs ∧ os = xs.map (actOf t) ∧ next = tailName t := by
  have hsub : (MethodDesc.toMethod (c, t)).subtasks = t.toTaskNetwork := rfl
  constructor
  · rintro ⟨tail, hwc, ⟨l, hlin, hseq, hlab⟩, rfl⟩
    rw [hsub] at hwc hlin hseq hlab
    have hprim_l : ∀ x ∈ l, x ∈ primIds t := by
      intro x hx
      have hxT : x ∈ t.toTaskNetwork.T := (hlin.2.1 x).1 (by cases tail <;> simp [hx])
      refine mem_primIds_of_not_abstract (mem_T_iff.1 hxT) ?_
      rintro ⟨cc, hcc⟩
      have hmem : t.toTaskNetwork.α x ∈ l.map t.toTaskNetwork.α := List.mem_map_of_mem hx
      rw [hseq] at hmem
      obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
      rw [← ha] at hcc
      exact absurd hcc (by simp)
    have hos : os = l.map (actOf t) := by
      have : l.map t.toTaskNetwork.α = (l.map (actOf t)).map (Sum.inl (β := ℕ)) := by
        rw [List.map_map]
        refine List.map_congr_left ?_
        intro x hx
        exact label_actOf (hprim_l x hx)
      rw [hseq] at this
      exact List.map_injective_iff.2 (fun _ _ h => Sum.inl_injective h) this
    cases htail : tail with
    | none =>
        subst htail
        have hnone : hasNextB t = false := by
          rcases hcase : hasNextB t with _ | _
          · rfl
          · exfalso
            obtain ⟨z, hz, hlabz⟩ := exists_compound hcase
            have hzT : z ∈ t.toTaskNetwork.T := mem_T_iff.2 hz
            have hzl : z ∈ l := by simpa using (hlin.2.1 z).2 hzT
            exact (not_isAbstractId_of_mem_primIds (hprim_l z hzl)) ⟨_, hlabz⟩
        refine ⟨l, ⟨hlin.1, ?_, hlin.2.2⟩, hos, by simp [tailName, hnone]⟩
        intro x
        refine ⟨fun hx => hprim_l x hx, fun hx => ?_⟩
        simpa using (hlin.2.1 x).2 (mem_T_iff.2 (mem_primIds.1 hx).1)
    | some p =>
        subst htail
        have hlabp : t.label p.1 = Sum.inr p.2 := hlab p rfl
        have hpids : p.1 ∈ t.ids := by
          have := hwc.tailMem p rfl
          exact mem_T_iff.1 this
        obtain ⟨hnext, hname⟩ := nextName_eq hreg hpids hlabp
        simp only [TaskNetwork.chainIds_some] at hlin
        have hnd : l.Nodup ∧ p.1 ∉ l := by
          have := hlin.1
          rw [List.nodup_append] at this
          exact ⟨this.1, fun hcon => this.2.2 p.1 hcon p.1 (by simp) rfl⟩
        refine ⟨l, ⟨hnd.1, ?_, ?_⟩, hos, by simp [tailName, hnext, hname]⟩
        · intro x
          refine ⟨fun hx => hprim_l x hx, fun hx => ?_⟩
          have hxT : x ∈ t.toTaskNetwork.T := mem_T_iff.2 (mem_primIds.1 hx).1
          have hxl : x ∈ l ++ [p.1] := (hlin.2.1 x).2 hxT
          rcases List.mem_append.1 hxl with h | h
          · exact h
          · simp only [List.mem_singleton] at h
            subst h
            exact absurd ⟨p.2, hlabp⟩ (not_isAbstractId_of_mem_primIds hx)
        · exact (List.pairwise_append.1 hlin.2.2).1
  · rintro ⟨xs, ⟨hnd, hmem, hpair⟩, rfl, rfl⟩
    have hseq : t.toTaskNetwork.IsActionSeq xs (xs.map (actOf t)) := by
      show xs.map t.toTaskNetwork.α = (xs.map (actOf t)).map Sum.inl
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro x hx
      exact label_actOf ((hmem x).1 hx)
    rcases hcase : hasNextB t with _ | _
    · refine ⟨none, ⟨t.toTaskNetwork_wf, by rintro p ⟨⟩, by rintro p ⟨⟩, by rintro p ⟨⟩, ?_⟩,
        ⟨xs, ⟨hnd, ?_, hpair⟩, hseq, by rintro p ⟨⟩⟩, by simp [tailName, hcase]⟩
      · intro x hx _
        rcases hlab : t.label x with a | cc
        · exact ⟨a, hlab⟩
        · exact absurd hlab (not_compound hcase (mem_T_iff.1 hx))
      · intro x
        simp only [TaskNetwork.chainIds_none]
        rw [hmem x]
        constructor
        · intro hx
          exact mem_T_iff.2 (mem_primIds.1 hx).1
        · intro hx
          refine mem_primIds_of_not_abstract (mem_T_iff.1 hx) ?_
          rintro ⟨cc, hcc⟩
          exact absurd hcc (not_compound hcase (mem_T_iff.1 hx))
    · obtain ⟨z, hz, hlabz, huniq⟩ := exists_unique_compound hreg hcase
      have hzT : z ∈ t.toTaskNetwork.T := mem_T_iff.2 hz
      have hzxs : z ∉ xs := by
        intro hcon
        exact (not_isAbstractId_of_mem_primIds ((hmem z).1 hcon)) ⟨_, hlabz⟩
      have hlast : ∀ x ∈ t.toTaskNetwork.T, x ≠ z → t.toTaskNetwork.ord x z :=
        fun x hx hxz => hreg.2 z hzT ⟨_, hlabz⟩ x hx hxz
      have hwc : t.toTaskNetwork.IsWeakChain (some (z, nextName t)) := by
        refine ⟨t.toTaskNetwork_wf, ?_, ?_, ?_, ?_⟩
        · rintro p ⟨rfl⟩; exact hzT
        · rintro p ⟨rfl⟩; exact hlabz
        · rintro p ⟨rfl⟩; exact hlast
        · intro x hx hxp
          have hnab : ¬ t.toTaskNetwork.IsAbstractId x := by
            intro hab
            exact hxp (z, nextName t) rfl (huniq x (mem_T_iff.1 hx) hab)
          rcases hlab : t.label x with a | cc
          · exact ⟨a, hlab⟩
          · exact absurd ⟨cc, hlab⟩ hnab
      refine ⟨some (z, nextName t), hwc, ⟨xs, ⟨?_, ?_, ?_⟩, hseq, ?_⟩, by simp [tailName, hcase]⟩
      · rw [TaskNetwork.chainIds_some]
        exact List.Nodup.append hnd (by simp) (by
          intro a ha hb
          simp only [List.mem_singleton] at hb
          subst hb
          exact hzxs ha)
      · intro x
        rw [TaskNetwork.chainIds_some, List.mem_append]
        constructor
        · rintro (hx | hx)
          · exact mem_T_iff.2 (mem_primIds.1 ((hmem x).1 hx)).1
          · simp only [List.mem_singleton] at hx
            subst hx
            exact hzT
        · intro hx
          by_cases hxz : x = z
          · exact Or.inr (by simp [hxz])
          · refine Or.inl ((hmem x).2 (mem_primIds_of_not_abstract (mem_T_iff.1 hx) ?_))
            intro hab
            exact hxz (huniq x (mem_T_iff.1 hx) hab)
      · rw [TaskNetwork.chainIds_some]
        refine List.pairwise_append.2 ⟨hpair, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        intro hcon
        have haT : a ∈ t.toTaskNetwork.T := mem_T_iff.2 (mem_primIds.1 ((hmem a).1 ha)).1
        have hab : a ≠ b := by
          intro hcon2
          exact hzxs (hcon2 ▸ ha)
        exact t.toTaskNetwork_wf.asymm hcon (hlast a haT hab)
      · rintro p ⟨rfl⟩
        exact hlabz

end TnDesc

end Syn

end HTN
