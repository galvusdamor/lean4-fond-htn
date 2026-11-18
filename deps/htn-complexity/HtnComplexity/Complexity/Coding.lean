import HtnComplexity.Complexity.Serial
import HtnComplexity.Complexity.InstPolyTime
import ComplexityTheory.Complexity.PolyTimeTM
import HtnComplexity.Complexity.BitCoding
/-!
# Polynomial time on descriptions, for an arbitrary coding

`HtnComplexity/Complexity/InstPolyTime.lean` fixes one coding of problem-instance
descriptions as bit strings — the binary digits of the Gödel number — and defines a translation
to be polynomial time when it acts on those codes as a function of Cobham's class.  Nothing in
the Karp–Lipton argument depends on *which* coding is used, only on the coding being injective
and computable, and the choice matters in practice:

* the Gödel coding `HTN.Syn.instBits` is easy to define but useless for writing translations
  down, and its length is exponential in the number of symbols of the description;
* the serialisation `HTN.Syn.instSer` of `HtnComplexity/Complexity/Serial.lean` is the
  coding one means when one says "polynomial time in the size of the input", and concrete
  translations *can* be exhibited for it (`HtnComplexity/Complexity/GuardFamily.lean`).

This file therefore makes the coding a parameter:

* `HTN.Syn.BitCoding α` — an injective computable coding of a type of descriptions as bit
  strings, with the two instances `HTN.Syn.codingSer` and `HTN.Syn.codingGodel`;
* `HTN.Syn.BitCoding.computable_of_code_eq` — the inverse comes for free: a function into `α`
  whose code is computable is computable, proved by an unbounded search that terminates because
  the coding is injective.  This is what replaces the explicit parser `HTN.Syn.instOfBits`
  available for the Gödel coding;
* `HTN.Syn.PolyTimeMap c` and `HTN.Syn.PolyTimeCode c` — the two notions of
  `InstPolyTime.lean`, relative to `c`, with the same closure properties, and
  `HTN.Syn.polyTimeMap_godel_iff` / `HTN.Syn.polyTimeCode_godel_iff` identifying them with the
  notions of that file at `c = codingGodel`.
-/

namespace HTN

namespace Syn

open PTime

namespace BitCoding

variable {α : Type} [Primcodable α] (c : BitCoding α)

/-- **A function whose code is computable is computable.**  The proof searches for the object
with the given code; the search terminates because such an object exists, and the object it
finds is the right one because the coding is injective.  This is the general form of the step
that turns a polynomial-time translation into a computable one. -/
theorem computable_of_code_eq {β : Type} [Primcodable β] {G : β → List Bool} (hG : Computable G)
    {f : β → α} (hf : ∀ b, G b = c.code (f b)) : Computable f := by
  classical
  -- the search: the first number coding an object whose code is `G b`
  set F : β → ℕ → Option α := fun b n =>
    (Encodable.decode (α := α) n).bind fun q => if c.code q = G b then some q else none with hF
  have hFc : Computable₂ F := by
    have hdec : Computable (fun p : β × ℕ => Encodable.decode (α := α) p.2) :=
      Computable.decode.comp Computable.snd
    have hbody : Computable₂ (fun (p : β × ℕ) (q : α) =>
        if c.code q = G p.1 then some q else none) := by
      have hdeceq : Primrec (fun p : List Bool × List Bool => decide (p.1 = p.2)) :=
        PrimrecPred.decide (Primrec.eq (α := List Bool))
      have hcond : Computable (fun r : (β × ℕ) × α => decide (c.code r.2 = G r.1.1)) :=
        hdeceq.to_comp.comp (Computable.pair (c.computable.comp Computable.snd)
          (hG.comp (Computable.fst.comp Computable.fst)))
      have hcase : Computable (fun r : (β × ℕ) × α =>
          if c.code r.2 = G r.1.1 then some r.2 else none) :=
        (Computable.cond hcond (Computable.option_some.comp Computable.snd)
          (Computable.const (none : Option α))).of_eq fun r => by
            by_cases h : c.code r.2 = G r.1.1 <;> simp [h]
      exact hcase.to₂
    exact (Computable.option_bind hdec hbody).to₂
  have hpart : Partrec fun b => Nat.rfindOpt (F b) := Partrec.rfindOpt hFc
  refine (hpart.of_eq fun b => ?_)
  have hmemn : f b ∈ F b (Encodable.encode (f b)) := by
    simp [hF, hf b]
  have hdom : (Nat.rfindOpt (F b)).Dom :=
    Nat.rfindOpt_dom.2 ⟨Encodable.encode (f b), f b, hmemn⟩
  have hget : (Nat.rfindOpt (F b)).get hdom ∈ Nat.rfindOpt (F b) := Part.get_mem hdom
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hget
  have hcode : c.code ((Nat.rfindOpt (F b)).get hdom) = G b := by
    simp only [hF, Option.mem_def, Option.bind_eq_some_iff] at hn
    obtain ⟨q, -, hq⟩ := hn
    by_cases h : c.code q = G b
    · rw [if_pos h] at hq
      rw [← Option.some_inj.1 hq]
      exact h
    · rw [if_neg h] at hq
      exact absurd hq (by simp)
  have heq : (Nat.rfindOpt (F b)).get hdom = f b :=
    c.injective (by rw [hcode, hf b])
  show Nat.rfindOpt (F b) = Part.some (f b)
  rw [← heq]
  exact Part.eq_some_iff.2 hget

end BitCoding

/-! ### The two codings of instance descriptions -/

/-- The binary code of the Gödel number, as a coding. -/
def codingGodel : BitCoding InstDesc :=
  ⟨instBits, instBits_injective, computable_instBits⟩

@[simp] theorem codingSer_code : codingSer.code = instSer := rfl

@[simp] theorem codingGodel_code : codingGodel.code = instBits := rfl

/-! ### Polynomial time relative to a coding -/

variable (c : BitCoding InstDesc)

variable {c}

/-- A polynomial-time translation is computable. -/
theorem PolyTimeMap.computable {f : InstDesc → InstDesc} (hf : PolyTimeMap c f) : Computable f := by
  obtain ⟨F, hF, hFf⟩ := hf
  exact c.computable_of_code_eq (hF.computable.comp c.computable) hFf

/-- A polynomial-time encoding is computable. -/
theorem PolyTimeCode.computable {enc : List Bool → InstDesc} (h : PolyTimeCode c enc) :
    Computable enc := by
  obtain ⟨F, hF, hFe⟩ := h
  exact c.computable_of_code_eq hF.computable hFe

/-- The identity translation is polynomial time. -/
theorem polyTimeMap_id : PolyTimeMap c _root_.id :=
  ⟨_root_.id, polyTimeFun_id, fun _ => rfl⟩

/-- Polynomial-time translations are closed under composition. -/
theorem PolyTimeMap.comp {f g : InstDesc → InstDesc} (hf : PolyTimeMap c f)
    (hg : PolyTimeMap c g) : PolyTimeMap c (fun q => f (g q)) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  refine ⟨fun x => F (G x), hF.comp hG, fun q => ?_⟩
  show F (G (c.code q)) = c.code (f (g q))
  rw [hGg q, hFf (g q)]

/-- Composing a polynomial-time encoding with a polynomial-time translation gives a
polynomial-time encoding — the step the Karp–Lipton argument makes. -/
theorem PolyTimeCode.compMap {f : InstDesc → InstDesc} {enc : List Bool → InstDesc}
    (hf : PolyTimeMap c f) (h : PolyTimeCode c enc) : PolyTimeCode c (fun w => f (enc w)) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGe⟩ := h
  refine ⟨fun w => F (G w), hF.comp hG, fun w => ?_⟩
  show F (G w) = c.code (f (enc w))
  rw [hGe w, hFf (enc w)]

/-! ### The notions of `InstPolyTime.lean` are the case of the Gödel coding -/

theorem polyTimeMap_godel_iff {f : InstDesc → InstDesc} :
    PolyTimeMap codingGodel f ↔ PolyTimeInst f := Iff.rfl

end Syn

end HTN
