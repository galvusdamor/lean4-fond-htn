import ComplexityTheory.Complexity.CobhamTM.VecIter
/-!
# Fixed-width codes of finite types, polynomial counters

* `blkCode` — a one-hot code of fixed width for the elements of a finite type, and `decBlk`,
  which reads such a code off the front of a string.  `cobObs_decBlk`: reading a code is a
  finite observation decided in Cobham's class, so it can drive `cobham_dispatch`.
* `cobham_flatMapBits` — replacing every bit of a string by a fixed word.
* `exists_cobham_poly` — for every polynomial `p` there is a function of the class whose output
  is at least `p` of the length of its first argument (a counter for `cobham_iterate`).
-/

namespace HTN.PTime.CobhamTM

open HTN.PTime

/-! ### One-hot codes -/

section Blk

variable {β : Type} [Fintype β] [DecidableEq β]

/-- The one-hot code of an element of a finite type: a string of length `card β`. -/
noncomputable def blkCode (b : β) : List Bool :=
  List.ofFn fun j : Fin (Fintype.card β) => decide (j = Fintype.equivFin β b)

theorem length_blkCode (b : β) : (blkCode b).length = Fintype.card β := by simp [blkCode]

theorem blkCode_injective : Function.Injective (blkCode (β := β)) := by
  intro a b h
  have h2 := congrArg (fun l => l[(Fintype.equivFin β a : ℕ)]?) h
  simp only [blkCode, List.getElem?_ofFn] at h2
  have hlt : (Fintype.equivFin β a : ℕ) < Fintype.card β := (Fintype.equivFin β a).isLt
  simp only [hlt, dite_true, Option.some.injEq, Fin.eta, decide_true] at h2
  have := of_decide_eq_true h2.symm
  exact (Fintype.equivFin β).injective (Fin.ext (congrArg Fin.val this))

open Classical in
/-- Reading a code off the front of a string, as a function of the prefix tests. -/
noncomputable def decTests (t : β → Bool) : Option β :=
  if h : ∃ b, t b = true then some (Classical.choose h) else none

/-- Reading a code off the front of a string. -/
noncomputable def decBlk (s : List Bool) : Option β :=
  decTests fun b => decide (blkCode b <+: s)

theorem prefix_blkCode_iff {a b : β} {r : List Bool} : blkCode a <+: blkCode b ++ r ↔ a = b := by
  constructor
  · intro h
    apply blkCode_injective
    have h1 : blkCode a <+: blkCode b ++ r := h
    have h2 : blkCode b <+: blkCode b ++ r := List.prefix_append _ _
    exact (List.prefix_of_prefix_length_le h1 h2 (by simp [length_blkCode])).eq_of_length
      (by simp [length_blkCode])
  · rintro rfl; exact List.prefix_append _ _

theorem decBlk_blkCode_append (b : β) (r : List Bool) : decBlk (blkCode b ++ r) = some b := by
  unfold decBlk decTests
  have hex : ∃ a, decide (blkCode a <+: blkCode b ++ r) = true := ⟨b, by simp⟩
  rw [dif_pos hex]
  congr 1
  have := Classical.choose_spec hex
  simpa [prefix_blkCode_iff] using this

theorem decBlk_nil : decBlk ([] : List Bool) = (none : Option β) := by
  unfold decBlk decTests
  rw [dif_neg]
  rintro ⟨b, hb⟩
  simp only [decide_eq_true_eq, List.prefix_nil] at hb
  have h1 := length_blkCode b
  rw [hb] at h1
  have h2 : 0 < Fintype.card β := Fintype.card_pos_iff.2 ⟨b⟩
  simp at h1
  omega

/-- **Reading a code is a finite observation decided in Cobham's class.** -/
theorem cobObs_decBlk {a : Fn} (ha : Cobham a) (o : Option β) :
    CobB fun args => decide (decBlk (a args) = o) := by
  have hpi := cobhamObs_pi (ι := β) (β := fun _ => Bool)
    (fun b args => decide (blkCode b <+: a args))
    (fun b c => (cobB_ite (cobB_startsWith (blkCode b) ha) (cobB_const (decide (true = c)))
      (cobB_const (decide (false = c)))).of_eq fun args => by
        by_cases h : blkCode b <+: a args <;> simp [h])
  exact cobhamObs_map _ hpi decTests o

end Blk


/-! ### Decoding a string of codes, block by block -/

section Decode

variable {β : Type} [Fintype β] [DecidableEq β]

/-- The step functions of the block decoder: the first component is the rest of the input,
the second the output so far. -/
noncomputable def decSteps (g : β → Bool) : List Fn :=
  [fun a => (a.getD 0 []).drop (Fintype.card β),
   fun a => match decBlk (a.getD 0 []) with
     | some b => a.getD 1 [] ++ [g b]
     | none => a.getD 1 []]

/-- The initial values of the block decoder. -/
def decInits : List Fn := [fun a => a.getD 0 [], fun _ => []]

/-- **The block decoder**: reads the codes of a list of elements and outputs one bit per
element. -/
noncomputable def decodeBlocks (g : β → Bool) : Fn := fun args =>
  ((stepV (decSteps g) args)^[(args.getD 0 []).length] (initV decInits args)).getD 1 []

theorem stepV_decSteps (g : β → Bool) (args : Args) (r o : List Bool) :
    stepV (decSteps g) args [r, o] =
      [r.drop (Fintype.card β), match decBlk r with
        | some b => o ++ [g b]
        | none => o] := by
  rfl

theorem iterate_decSteps_bound (g : β → Bool) (args : Args) (t : ℕ) :
    ∃ r o, (stepV (decSteps g) args)^[t] (initV decInits args) = [r, o] ∧
      r.length ≤ (args.getD 0 []).length ∧ o.length ≤ t := by
  induction t with
  | zero => exact ⟨args.getD 0 [], [], rfl, le_rfl, le_rfl⟩
  | succ t ih =>
    obtain ⟨r, o, e, hr, ho⟩ := ih
    rw [Function.iterate_succ_apply', e, stepV_decSteps]
    refine ⟨_, _, rfl, le_trans (by rw [List.length_drop]; omega) hr, ?_⟩
    split
    · simp only [List.length_append, List.length_singleton]; omega
    · omega

theorem iterate_decSteps_spec (g : β → Bool) (l : List β) (rest : Args) (t : ℕ) :
    (stepV (decSteps g) (l.flatMap blkCode :: rest))^[t]
        (initV decInits (l.flatMap blkCode :: rest)) =
      [(l.drop t).flatMap blkCode, (l.take t).map g] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, stepV_decSteps]
    cases h : l.drop t with
    | nil =>
      have hl : l.length ≤ t := by simpa using h
      simp [decBlk_nil, List.take_of_length_le hl, List.take_of_length_le (show l.length ≤ t + 1 by omega),
        List.drop_eq_nil_of_le (show l.length ≤ t + 1 by omega)]
    | cons b rest' =>
      have h1 : l.drop (t + 1) = rest' := by
        rw [← List.drop_drop, h]; rfl
      have h2 : l.take (t + 1) = l.take t ++ [b] := by
        have e := List.take_append_drop t l
        rw [h] at e
        have ht : t ≤ l.length := by
          by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at h; cases h
        have hlen : (l.take t).length = t := by rw [List.length_take]; omega
        conv_lhs => rw [← e, show t + 1 = (l.take t).length + 1 by omega,
          List.take_length_add_append]
        simp
      rw [h1, h2, List.flatMap_cons, decBlk_blkCode_append, List.drop_left' (length_blkCode b)]
      simp

theorem cobham_decodeBlocks (g : β → Bool) : Cobham (decodeBlocks g) := by
  have hsteps : ∀ f ∈ decSteps g, Cobham f := by
    intro f hf
    simp only [decSteps, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact cobham_dropConst _ (Cobham.proj 0)
    · refine (cobham_dispatch (fun a => decBlk (a.getD 0 []))
        (fun o => cobObs_decBlk (Cobham.proj 0) o)
        (fun o => match o with
          | some b => fun a => a.getD 1 [] ++ [g b]
          | none => fun a => a.getD 1 [])
        (fun o => match o with
          | some b => cobham_appendConst (Cobham.proj 1) _
          | none => Cobham.proj 1)).of_fun_eq fun a => ?_
      cases (decBlk (List.getD a 0 []) : Option β) <;> rfl
  have hinits : ∀ f ∈ (decInits : List Fn), Cobham f := by
    intro f hf
    simp only [decInits, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact Cobham.proj 0
    · exact Cobham.empty
  exact cobham_iterVec decInits (decSteps g) rfl hinits hsteps (Cobham.proj 0) (Cobham.proj 0)
    (fun args t ht c hc => by
      obtain ⟨r, o, e, hr, ho⟩ := iterate_decSteps_bound g args t
      rw [e] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hr
      · exact le_trans ho ht) 1

theorem decodeBlocks_spec (g : β → Bool) (l : List β) (rest : Args) :
    decodeBlocks g (l.flatMap blkCode :: rest) = l.map g := by
  unfold decodeBlocks
  rw [List.getD_cons_zero, iterate_decSteps_spec]
  have hl : l.length ≤ (l.flatMap blkCode).length := by
    rcases Nat.eq_zero_or_pos (Fintype.card β) with h0 | h0
    · have : IsEmpty β := Fintype.card_eq_zero_iff.1 h0
      cases l with
      | nil => simp
      | cons b _ => exact (IsEmpty.false b).elim
    · rw [List.length_flatMap]
      simp only [length_blkCode, List.map_const', List.sum_replicate, smul_eq_mul]
      exact Nat.le_mul_of_pos_right _ h0
  rw [List.take_of_length_le hl]
  rfl

end Decode

/-! ### Replacing every bit by a fixed word -/

theorem cobham_flatMapBits (g : Bool → List Bool) {a : Fn} (ha : Cobham a) :
    Cobham fun args => (a args).flatMap g := by
  set M := (g false).length + (g true).length with hM
  have hb : Cobham (brnFn (fun _ => []) (fun args => g false ++ args.getD 1 [])
      (fun args => g true ++ args.getD 1 [])) := by
    refine Cobham.brn Cobham.empty (cobham_constAppend (Cobham.proj 1) _)
      (cobham_constAppend (Cobham.proj 1) _)
      (cobham_c2 Cobham.smash (Cobham.proj 0) (cobham_const (List.replicate M false)))
      fun args => ?_
    simp only [brnFn]
    suffices ∀ x v, (brnAux (fun _ => []) (fun args => g false ++ args.getD 1 [])
        (fun args => g true ++ args.getD 1 []) x v) = x.flatMap g by
      rw [this]
      simp only [smashFn, List.getD_cons_zero, List.getD_cons_succ, List.length_replicate,
        PTime.proj]
      generalize args.getD 0 [] = x
      induction x with
      | nil => simp
      | cons b x ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        cases b <;> simp only [Nat.succ_mul] <;> omega
    intro x v
    induction x with
    | nil => simp [brnAux]
    | cons b x ih =>
      cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ,
        List.getD_cons_zero, ih]; simp)
  refine (cobham_c1 hb ha).of_fun_eq fun args => ?_
  simp only [brnFn, List.getD_cons_zero, List.tail_cons]
  generalize a args = x
  induction x with
  | nil => simp [brnAux]
  | cons b x ih =>
    cases b <;> (simp only [brnAux, cond_false, cond_true, List.getD_cons_succ,
        List.getD_cons_zero, ih] at ih ⊢; simp)

/-! ### Polynomial counters -/

/-- **Polynomial counters.**  For every polynomial `p` there is a function of the class whose
output on `x :: _` has length exactly `p (|x|)`. -/
theorem exists_cobham_poly (p : Polynomial ℕ) :
    ∃ cnt : Fn, Cobham cnt ∧ ∀ args, (cnt args).length = p.eval (args.getD 0 []).length := by
  induction p using Polynomial.induction_on with
  | C a => exact ⟨fun _ => List.replicate a false, cobham_const _, fun _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨c₁, h₁, e₁⟩ := hp
    obtain ⟨c₂, h₂, e₂⟩ := hq
    exact ⟨fun args => c₁ args ++ c₂ args, cobham_append' h₁ h₂, fun args => by simp [e₁, e₂]⟩
  | monomial n a ih =>
    obtain ⟨c, hc, e⟩ := ih
    refine ⟨fun args => smashFn [c args, args.getD 0 []], cobham_c2 Cobham.smash hc
      (Cobham.proj 0), fun args => ?_⟩
    simp [smashFn, e, pow_succ, mul_assoc]

end HTN.PTime.CobhamTM
