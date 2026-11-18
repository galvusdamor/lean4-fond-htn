import FondHtn.AcycHard.HierInv
import FondHtn.MethodPoliciesStrong
import FondHtn.FixedMethodsLemmas
/-!
# Single-method hierarchies: solvability is the chain game of the expansions

For a FOND HTN problem whose methods realise a hierarchy specification (`FOND.AcycHard.Fit`)
and whose initial network satisfies the invariant with the expansions `ctlT`, `poolT`:

* **`FOND.AcycHard.strongOD_iff_hier`** — strong OD solvability (fixed methods) is the chain
  game `CWin` on the expansions;
* **`FOND.AcycHard.mpAndOr_iff_hier`** — so is strong solvability with method-based policies
  (the AND/OR characterisation `MPAndOr`): decompositions never change the expansions.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace AcycHard

open HTN

variable {F A C : Type} [DecidableEq A] {CA PA : Type}

/-- **Empty chains do not matter in the chain game.** -/
theorem cwin_cons_nil {δC : CA → Action F} {δP : PA → Action F} [DecidableEq PA] :
    ∀ {ctl : List CA} {M : Multiset (List PA)} {s : Set F},
      CWin δC δP ctl ([] ::ₘ M) s ↔ CWin δC δP ctl M s := by
  intro ctl M s
  constructor
  · intro h
    generalize hM : [] ::ₘ M = M' at h
    induction h generalizing M with
    | done h => subst hM; exact .done fun c hc => h c (Multiset.mem_cons_of_mem hc)
    | ctl happ _ ih => exact .ctl happ fun s' hs' => ih s' hs' hM
    | @pool ctl M' s a c hc happ _ ih =>
      subst hM
      have hc' : a :: c ∈ M := (Multiset.mem_cons.1 hc).resolve_left (by simp)
      refine .pool hc' happ fun s' hs' => ih s' hs' ?_
      rw [Multiset.erase_cons_tail _ (by simp), Multiset.cons_swap]
  · intro h
    induction h with
    | done h =>
      refine .done fun c hc => ?_
      rcases Multiset.mem_cons.1 hc with rfl | hc
      · rfl
      · exact h c hc
    | ctl happ _ ih => exact .ctl happ ih
    | @pool ctl M s a c hc happ _ ih =>
      refine .pool (Multiset.mem_cons_of_mem hc) happ fun s' hs' => ?_
      rw [Multiset.erase_cons_tail _ (by simp), Multiset.cons_swap]
      exact ih s' hs'

theorem cwin_filt {δC : CA → Action F} {δP : PA → Action F} [DecidableEq PA] {ctl : List CA}
    {M : Multiset (List PA)} {s : Set F} (l : List PA) :
    CWin δC δP ctl (HSpec.filt l + M) s ↔ CWin δC δP ctl (l ::ₘ M) s := by
  unfold HSpec.filt
  split_ifs with hl
  · subst hl; rw [zero_add, cwin_cons_nil]
  · rw [Multiset.singleton_add]

variable (P : Problem F A C ℕ) {H : HSpec A C}

/-- Primitive networks: belief solvability gives the method-based AND/OR game. -/
theorem mpAndOr_of_beliefSolvable {tn : TaskNetwork ℕ A C} {s : Set F} (h : P.BeliefSolvable tn s) :
    P.MPAndOr tn s := by
  induction h with
  | empty hT => exact .empty hT
  | step hu hα happ _ ih => exact .prim hu hα happ ih

theorem mpAndOr_of_decomposesTo {tn tn' : TaskNetwork ℕ A C} {s : Set F}
    (hd : HTN.DecomposesTo P.methods tn tn') (h : P.MPAndOr tn' s) : P.MPAndOr tn s := by
  induction hd using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hs _ ih => obtain ⟨t, m, hs⟩ := hs; exact .decomp hs ih

/-- The chains of an invariant network contain set-kind tasks only alone. -/
theorem shape_nonset {cs : List (Ch ℕ A C)} (hsh : Shape H cs) {k : ℕ} (hk : k < cs.length)
    {a : A} {labs : List (A ⊕ C)} (hc : cs[k].2 = .inl a :: labs) : ∀ x ∈ cs[k].2, H.NonSet x := by
  intro x hx d rfl
  by_contra hd
  obtain ⟨-, he⟩ := hsh k hk d hx (by simpa using hd)
  rw [hc] at he; simp at he

/-- **Method-based AND/OR game, soundness**: it is won only if the chain game of the expansions
is won. -/
theorem cwin_of_mpAndOr (hfit : Fit P H) {tn : TaskNetwork ℕ A C} {s : Set F} (h : P.MPAndOr tn s) :
    ∀ {ctlT : List A} {poolT : Multiset (List A)}, HInv H tn ctlT poolT →
      CWin P.δ P.δ ctlT poolT s := by
  induction h with
  | @empty tn s hT =>
    intro ctlT poolT hinv
    obtain ⟨cs, h0, huc, -, hctl, hpool⟩ := hinv
    have hnil : ∀ j (hj : j < cs.length), cs[j].1 = [] := by
      intro j hj
      cases hcj : cs[j].1 with
      | nil => rfl
      | cons x l =>
        have := (huc.mem x).2 ⟨j, hj, by rw [hcj]; simp⟩
        rw [hT] at this; simp at this
    have hlab : ∀ j (hj : j < cs.length), cs[j].2 = [] := by
      intro j hj; rw [← huc.lab j hj, hnil j hj]; rfl
    rw [← hctl, ← hpool, hlab 0 h0]
    have : poolE H cs = 0 := by
      rw [poolE]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hch
      rw [List.getElem_tail, hlab _ (by simp at hi; omega), H.exC_nil]
    rw [this]
    exact .done fun c hc => absurd hc (Multiset.notMem_zero _)
  | @prim tn s t a hu hα happ hall ih =>
    intro ctlT poolT hinv
    obtain ⟨cs, h0, huc, hsh, hctl, hpool⟩ := hinv
    obtain ⟨k, hk, htk⟩ := (huc.mem t).1 hu.1
    obtain ⟨rest, hrest⟩ := huc.head_of_unconstrained hu hk htk
    have hlk : cs[k].2 = .inl a :: rest.map tn.α := by rw [← huc.lab k hk, hrest]; simp [hα]
    have hck : cs[k] = (t :: rest, .inl a :: rest.map tn.α) := by rw [← hrest, ← hlk]
    have huc' := huc.progress hk hck
    have hsh' : Shape H (cs.set k (rest, rest.map tn.α)) := by
      intro j hj d hd hdS
      simp only [List.getElem_set] at hd ⊢
      split_ifs at hd ⊢ with hjk
      · subst hjk
        have := shape_nonset hsh hk hlk (.inr d) (by rw [hlk]; exact List.mem_cons_of_mem _ hd) d rfl
        rw [this] at hdS; cases hdS
      · exact hsh j (by simpa using hj) d hd hdS
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · -- the control chain
      rw [← hctl, hlk, List.flatMap_cons, HSpec.exI_inl, List.singleton_append]
      refine .ctl happ fun s' hs' => ih s' hs' ⟨_, by simpa using h0, huc', hsh', ?_, ?_⟩
      · simp [List.getElem_set]
      · rw [← hpool, poolE, poolE]
        cases cs with
        | nil => simp at h0
        | cons c0 cs => rfl
    · -- a pool chain
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      set rest' := (rest.map tn.α).flatMap H.exI with hrest'
      have hns := shape_nonset hsh hk hlk
      have hex : H.exC cs[k' + 1].2 = {a :: rest'} := by
        rw [H.exC_nonset hns, hlk, List.flatMap_cons, HSpec.exI_inl]
        simp [HSpec.filt, hrest']
      have hns' : ∀ x ∈ rest.map tn.α, H.NonSet x := fun x hx => hns x (by rw [hlk]; simp [hx])
      have hex' : H.exC (rest.map tn.α) = HSpec.filt rest' := H.exC_nonset hns'
      have hk' : k' < cs.tail.length := by simp; omega
      have e := sum_set (fun ch : Ch ℕ A C => H.exC ch.2) cs.tail k' hk' (rest, rest.map tn.α)
      have e2 : H.exC (cs.tail[k']'hk').2 = {a :: rest'} := by
        have : cs.tail[k']'hk' = cs[k' + 1] := by simp
        rw [this, hex]
      rw [e2] at e
      simp only at e
      rw [hex', show (cs.tail.map fun ch => H.exC ch.2).sum = poolT from hpool] at e
      -- `e : poolE' + {a :: rest'} = poolT + filt rest'`
      set poolT' := ((cs.tail.set k' (rest, rest.map tn.α)).map fun ch => H.exC ch.2).sum with hpT'
      have hmem : a :: rest' ∈ poolT := by
        have : a :: rest' ∈ poolT' + {a :: rest'} := by simp
        rw [e] at this
        rcases Multiset.mem_add.1 this with h | h
        · exact h
        · unfold HSpec.filt at h; split_ifs at h with h'
          · simp at h
          · simp at h
      have hsplit : poolT' = HSpec.filt rest' + poolT.erase (a :: rest') := by
        have e' : poolT' + {a :: rest'} = (HSpec.filt rest' + poolT.erase (a :: rest')) + {a :: rest'} :=
          calc poolT' + {a :: rest'} = poolT + HSpec.filt rest' := e
            _ = ((a :: rest') ::ₘ poolT.erase (a :: rest')) + HSpec.filt rest' := by
              rw [Multiset.cons_erase hmem]
            _ = (HSpec.filt rest' + poolT.erase (a :: rest')) + {a :: rest'} := by
              rw [← Multiset.singleton_add]; abel
        exact add_right_cancel e'
      refine .pool hmem happ fun s' hs' => ?_
      rw [← cwin_filt]
      refine ih s' hs' ⟨_, by simpa using h0, huc', hsh', ?_, ?_⟩
      · rw [← hctl]; simp [List.getElem_set]
      · rw [poolE, tail_set_succ, ← hsplit]
  | decomp hd _ ih => intro ctlT poolT hinv; exact ih (HInv.step P hfit hd hinv)

section Main

variable [Inhabited A] (hfit : Fit P H) (R : C → Prop) (hRc : ∀ c d, R c → .inr d ∈ H.body c → R d)
  (hex : ∀ c, R c → ∃ m ∈ P.methods, m.abstractTask = c)
include hfit hRc hex

theorem cwin_iff_of_primitive {tn : TaskNetwork ℕ A C} (hprim : tn.IsPrimitive) {ctlT : List A}
    {poolT : Multiset (List A)} (hinv : HInv H tn ctlT poolT) (s : Set F) :
    P.BeliefSolvable tn s ↔ CWin P.δ P.δ ctlT poolT s := by
  obtain ⟨ctl, pool, ℓ, hch, e1, e2⟩ := hinv.isChains (fun t ht => hprim t ht)
  rw [beliefSolvable_iff_cwin P hch s, e1, e2]

/-- **Method-based policies**: the AND/OR game is the chain game of the expansions. -/
theorem mpAndOr_iff_hier {tn : TaskNetwork ℕ A C} {s : Set F} {ctlT : List A}
    {poolT : Multiset (List A)} (hinv : HInv H tn ctlT poolT)
    (hR : ∀ t ∈ tn.T, ∀ c, tn.α t = .inr c → R c) :
    P.MPAndOr tn s ↔ CWin P.δ P.δ ctlT poolT s := by
  refine ⟨fun h => cwin_of_mpAndOr P hfit h hinv, fun h => ?_⟩
  obtain ⟨tn', hd, hprim⟩ := exists_primitive P hfit R hRc hex _ tn rfl hR
  have hinv' := HInv.decomposesTo P hfit hd hinv
  exact mpAndOr_of_decomposesTo P hd (mpAndOr_of_beliefSolvable P
    ((cwin_iff_of_primitive P hfit R hRc hex hprim hinv' s).2 h))

/-- **Fixed methods**: strong OD solvability is the chain game of the expansions. -/
theorem strongOD_iff_hier {ctlT : List A} {poolT : Multiset (List A)}
    (hinv : HInv H P.tnI ctlT poolT) (hR : ∀ t ∈ P.tnI.T, ∀ c, P.tnI.α t = .inr c → R c) :
    P.StrongODSolvable ↔ CWin P.δ P.δ ctlT poolT P.init := by
  rw [Problem.strongODSolvable_iff_fmSolvableDB]
  constructor
  · rintro ⟨tn, ⟨hd, hprim⟩, hb⟩
    exact (cwin_iff_of_primitive P hfit R hRc hex hprim (HInv.decomposesTo P hfit hd hinv) _).1 hb
  · intro h
    obtain ⟨tn', hd, hprim⟩ := exists_primitive P hfit R hRc hex _ P.tnI rfl hR
    exact ⟨tn', ⟨hd, hprim⟩, (cwin_iff_of_primitive P hfit R hRc hex hprim
      (HInv.decomposesTo P hfit hd hinv) _).2 h⟩

end Main

end AcycHard

end FOND
