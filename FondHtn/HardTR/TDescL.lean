import FondHtn.HardTR.TDesc
/-!
# CB22 Thm 5: properties of the description

Injectivity of the names, validity, the actions of the described problem and its initial state.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TD

open TL TT TE HardMP HTN HTN.Syn HTN.Article AcycHard.Sav

variable {S : Type} {cS : S → ℕ}

/-! ## Injectivity -/

theorem toNat_inj {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

theorem two_toNat_inj {a b c d : Bool} (h : 2 * a.toNat + b.toNat = 2 * c.toNat + d.toNat) :
    a = c ∧ b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem four_toNat_inj {a b c d e f : Bool}
    (h : 4 * a.toNat + 2 * b.toNat + c.toNat = 4 * d.toNat + 2 * e.toNat + f.toNat) :
    a = d ∧ b = e ∧ c = f := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> simp_all

theorem codeOG_inj : Function.Injective codeOG := by
  intro a b h; cases a <;> cases b <;> simp_all [codeOG]

theorem codeSp_inj : Function.Injective codeSp := by
  intro a b h
  rcases a with _ | ⟨a1, a2⟩ <;> rcases b with _ | ⟨b1, b2⟩ <;> simp_all [codeSp, Nat.pair_eq_pair]

theorem codeOp_inj : Function.Injective codeOp := by
  intro a b h
  cases a <;> cases b <;> simp only [codeOp, Nat.pair_eq_pair] at h <;> (try omega)
  · obtain ⟨-, h1, h2⟩ := h
    obtain ⟨h3, h4⟩ := two_toNat_inj h2
    rw [codeOG_inj h1, h3, h4]
  · obtain ⟨-, h1, h2⟩ := h
    obtain ⟨h3, h4, h5⟩ := four_toNat_inj h1
    rw [h3, h4, h5, codeSp_inj h2]
  · rw [toNat_inj h.2]
  · rw [toNat_inj h.2]

theorem codeEn_inj (hS : Function.Injective cS) : Function.Injective (codeEn cS) := by
  intro a b h
  cases a <;> cases b <;> simp only [codeEn, Nat.pair_eq_pair] at h <;> (try omega)
  · rw [hS h.2]
  · obtain ⟨-, h1, h2, h3, h4⟩ := h
    rw [toNat_inj h1, hS h2, hS h3, hS h4]

theorem nmA_inj (hS : Function.Injective cS) : Function.Injective (nmA cS) := by
  intro a b h
  cases a <;> cases b <;> simp only [nmA, Nat.pair_eq_pair] at h <;> (try omega)
  · obtain ⟨-, h1, h2⟩ := h; obtain ⟨h3, h4⟩ := two_toNat_inj h1; rw [h3, h4, h2]
  · obtain ⟨h3, h4⟩ := two_toNat_inj h.2; rw [h3, h4]
  · obtain ⟨-, h1, h2⟩ := h; obtain ⟨h3, h4⟩ := two_toNat_inj h1; rw [h3, h4, h2]
  · obtain ⟨-, h1, h2⟩ := h; rw [toNat_inj h1, codeOp_inj h2]
  · obtain ⟨-, h1, h2⟩ := h; rw [toNat_inj h1, h2]
  · rw [toNat_inj h.2]
  · obtain ⟨-, h1, h2⟩ := h; rw [toNat_inj h1, codeEn_inj hS h2]
  · rw [toNat_inj h.2]
  · rw [toNat_inj h.2]
  · rfl

theorem nmN_inj : Function.Injective nmN := by
  intro a b h
  cases a <;> cases b <;> simp only [nmN, Nat.pair_eq_pair] at h <;> (try omega) <;> (try rfl)
  · rw [toNat_inj h.2]
  · rw [toNat_inj h.2]
  · obtain ⟨-, h1, h2⟩ := h; rw [toNat_inj h1, h2]
  · obtain ⟨-, h1, h2⟩ := h; rw [toNat_inj h1, h2]
  · rw [toNat_inj h.2]
  · rw [toNat_inj h.2]
  · obtain ⟨h3, h4⟩ := two_toNat_inj h.2; rw [h3, h4]
  · obtain ⟨-, h1, h2⟩ := h; obtain ⟨h3, h4⟩ := two_toNat_inj h1; rw [h3, h4, h2]
  · rw [toNat_inj h.2]

/-! ## Validity -/

variable (cS) (X : Spec S) (allS : List S) (ops : List Op) (ens : List (En S))

/-- The declared actions. -/
def Dec (a : Act Op (En S)) : Prop := a ∈ acts X ops ens

theorem mem_acts_iff {a : Act Op (En S)} : a ∈ acts X ops ens ↔
    (∃ p k b, k < mm X ∧ a = .wb p k b) ∨ (∃ p k b, k < mm X ∧ a = .rb p k b) ∨
    (∃ p k, k < mm X ∧ a = .inc p k) ∨ (∃ p γ, a = .rv p γ) ∨ (∃ p, a = .wrap p) ∨
    (∃ p, a = .nrd p) ∨ (∃ p, a = .dr p) ∨ (∃ p o, o ∈ ops ∧ a = .op p o) ∨
    (∃ p e, e ∈ ens ∧ a = .rend p e) ∨ a = .fin := by
  constructor
  · intro h
    simp only [acts, actsP, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.mem_map, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with ((((⟨k, hk, h⟩ | h) | ⟨o, ho, rfl⟩) | ⟨e, he, rfl⟩) |
      (((⟨k, hk, h⟩ | h) | ⟨o, ho, rfl⟩) | ⟨e, he, rfl⟩)) | rfl
    all_goals (try rcases h with rfl | rfl | rfl | rfl | rfl) <;> simp_all
  · rintro (⟨p, k, b, hk, rfl⟩ | ⟨p, k, b, hk, rfl⟩ | ⟨p, k, hk, rfl⟩ | ⟨p, γ, rfl⟩ | ⟨p, rfl⟩ |
      ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, o, ho, rfl⟩ | ⟨p, e, he, rfl⟩ | rfl) <;>
      (try cases p) <;> (try cases b) <;> (try cases γ) <;>
      simp_all [acts, actsP]

/-- The shape of a method: a sequence or set body whose actions are declared. -/
def Shape (m : MethodDesc) : Prop :=
  ∃ ls : List (Bool × ℕ), (m.2 = seqTn ls ∨ m.2 = setTn ls) ∧
    ∀ q ∈ ls, q.1 = false → ∃ a ∈ acts X ops ens, q.2 = nmA cS a

theorem shape_seq (c : ℕ) {ls : List (Bool × ℕ)}
    (h : ∀ q ∈ ls, q.1 = false → ∃ a ∈ acts X ops ens, q.2 = nmA cS a) : Shape cS X ops ens (c, seqTn ls) :=
  ⟨ls, Or.inl rfl, h⟩

theorem shape_set (c : ℕ) {ls : List (Bool × ℕ)}
    (h : ∀ q ∈ ls, q.1 = false → ∃ a ∈ acts X ops ens, q.2 = nmA cS a) : Shape cS X ops ens (c, setTn ls) :=
  ⟨ls, Or.inr rfl, h⟩

theorem lbl_ok {ls : List (Bool × ℕ)} (h : ∀ q ∈ ls, q.1 = false → ∃ a ∈ acts X ops ens, q = lA cS a) :
    ∀ q ∈ ls, q.1 = false → ∃ a ∈ acts X ops ens, q.2 = nmA cS a := by
  intro q hq hf
  obtain ⟨a, ha, rfl⟩ := h q hq hf
  exact ⟨a, ha, rfl⟩

/-- **Every method has the shape.** -/
theorem meths_shape : ∀ m ∈ meths cS X ops ens, Shape cS X ops ens m := by
  simp only [meths, methsP, List.forall_mem_cons, List.forall_mem_append, List.forall_mem_flatMap,
    List.forall_mem_map, List.mem_range, List.forall_mem_nil, and_true, implies_true]
  repeat' (first | apply And.intro | intro)
  all_goals first
    | (exfalso; simp_all; done)
    | exact shape_seq _ _ _ _ _ (lbl_ok _ _ _ _ (by
        intro q hq hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> simp only [lA, lN] at hf ⊢ <;>
          first | (simp at hf; done) | exact ⟨_, by simp_all [mem_acts_iff], rfl⟩))
    | exact shape_set _ _ _ _ _ (lbl_ok _ _ _ _ (by
        intro q hq hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> simp only [lA, lN] at hf ⊢ <;>
          first | (simp at hf; done) | exact ⟨_, by simp_all [mem_acts_iff], rfl⟩))
    | exact shape_seq _ _ _ _ _ (by simp)

/-! ## Validity -/

variable (σ₀ : S)

theorem actions_desc : (desc cS X allS ops ens σ₀).actions =
    ((acts X ops ens).map fun a => toFAct (nmA cS a) (aspec cS X allS a)).dedup := by
  simp only [desc, FProbDesc.actions]

theorem methods_desc : (desc cS X allS ops ens σ₀).methods = meths cS X ops ens := by
  simp only [desc, FProbDesc.methods]

theorem tnI_desc : (desc cS X allS ops ens σ₀).tnI = seqTn [lN .main] := by
  simp only [desc, FProbDesc.tnI]

theorem init_desc : (desc cS X allS ops ens σ₀).init = curF none :: (bootFields cS σ₀).map fact := by
  simp only [desc, FProbDesc.init]

theorem mem_actions {x : FActDesc} : x ∈ (desc cS X allS ops ens σ₀).actions ↔
    ∃ a ∈ acts X ops ens, x = toFAct (nmA cS a) (aspec cS X allS a) := by
  rw [actions_desc, List.mem_dedup, List.mem_map]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩⟩

theorem declared_of_mem {a : Act Op (En S)} (ha : a ∈ acts X ops ens) :
    (desc cS X allS ops ens σ₀).Declared (nmA cS a) := by
  unfold FProbDesc.Declared
  rw [List.mem_map]
  exact ⟨_, (mem_actions cS X allS ops ens σ₀).2 ⟨a, ha, rfl⟩, rfl⟩

theorem effs_aspec_ne (a : Act Op (En S)) : (aspec cS X allS a).effs ≠ [] := by
  cases a with
  | rend p e => cases e <;> simp [aspec, ASpec.effs, endSpec]
  | _ => simp [aspec, ASpec.effs]

/-- **The description is well formed.** -/
theorem valid (hS : Function.Injective cS) : (desc cS X allS ops ens σ₀).Valid where
  names_nodup := by
    rw [actions_desc]
    refine (List.nodup_dedup _).map_on fun x hx y hy h => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hx)
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hy)
    have : a = b := nmA_inj hS h
    rw [this]
  effs_ne := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := (mem_actions cS X allS ops ens σ₀).1 hx
    simpa [toFAct, FActDesc.effs] using effs_aspec_ne cS X allS a
  tnI := by
    rw [tnI_desc]
    exact seqTn_valid (by simp [lN])
  methods := by
    intro m hm
    rw [methods_desc] at hm
    obtain ⟨ls, hls, hok⟩ := meths_shape cS X ops ens m hm
    have hprim : ∀ q ∈ ls, q.1 = false → (desc cS X allS ops ens σ₀).Declared q.2 := by
      intro q hq hf
      obtain ⟨a, ha, he⟩ := hok q hq hf
      rw [he]; exact declared_of_mem cS X allS ops ens σ₀ ha
    rcases hls with h | h <;> rw [h]
    · exact seqTn_valid hprim
    · exact setTn_valid hprim

end TD

end HardTR

end FOND
