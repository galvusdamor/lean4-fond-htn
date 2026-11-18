import ComplexityTheory.Complexity.CobhamTM.CobhamToTM
import ComplexityTheory.Complexity.Basic
/-!
# Polynomial time, defined by Mathlib's Turing machines

This file fixes the **official notion of a polynomial-time function** of the development:

    HTN.PTime.PolyTimeFun F :=
      Nonempty (Turing.TM2ComputableInPolyTime finEncodingListBool finEncodingListBool F)

i.e. `F : List Bool → List Bool` is computed by a multi-stack Turing machine of Mathlib
(`Turing.FinTM2`) within a polynomial number of steps, bit strings being written on the tape as
themselves (`HTN.PTime.CobhamTM.finEncodingListBool`, alphabet `Bool`).  (`Nonempty` because
Mathlib's `TM2ComputableInPolyTime` is a structure carrying the machine, i.e. data.)

Every polynomial-time notion built on `PolyTimeFun` — the instance translations of the
compilability notions (`HTN.Syn.PolyTimeMap`, `HTN.Syn.PolyTimeCode`, `HTN.Syn.PolyTimePred`,
`HTN.Syn.PolyTimeInst`, `HTN.Syn.PolyTimeEnc`) and the notions of classical complexity theory
(`HTN.Syn.InP`, `HTN.Syn.InNP`, `HTN.Syn.ReducesToPartition`, `HTN.Syn.Coded.PolyRed`) — is
therefore a statement about Turing machines.

Proofs that concrete functions are polynomial time are still carried out in Cobham's class: by
**Cobham's theorem** (`HTN.PTime.CobhamTM.cobhamFun_iff_tm2ComputableInPolyTime`) the two notions
agree, `HTN.PTime.polyTimeFun_iff_cobhamFun`, and `HTN.PTime.PolyTimeFun.of_cobham` /
`HTN.PTime.PolyTimeFun.cobham` move between them.

## Glue for other encodings

Mathlib's notion is relative to encodings `ea : FinEncoding α`, `eb : FinEncoding β` of the
objects themselves.  For encodings over a binary alphabet (`ea.Γ ≃ Bool`), the last section shows
that computability in polynomial time *with respect to these encodings* is the same as the
existence of a polynomial-time function on bit strings that maps codes to codes:

* `HTN.PTime.tm2ComputableInPolyTime_iff` — for arbitrary `ea`, `eb` with binary alphabets,
  `Nonempty (TM2ComputableInPolyTime ea eb f) ↔
    ∃ F, PolyTimeFun F ∧ ∀ a, F ((ea.encode a).map ia) = (eb.encode (f a)).map ib`;
* `HTN.PTime.finEncodingOfBits` — the Mathlib encoding defined by an injective bit coding
  `code : α → List Bool` (decoding: the partial inverse), and
  `HTN.PTime.tm2ComputableInPolyTime_bits_iff`, the specialisation of the previous theorem to it.

The direction "machine ⇒ bit function" is not a mere restatement: the machine is only known to
halt in polynomial time on *codes*, while `PolyTimeFun` asks for a function on *all* bit strings.
It goes through the clocked simulation `HTN.PTime.CobhamTM.exists_cobham_of_outputsOn`, which
runs the machine for a polynomial number of steps on every input.
-/

namespace HTN.PTime

open Turing Computability CobhamTM

/-! ### The official notion -/

/-- **Cobham's theorem, in the form used by the development**: a function is polynomial time iff
it is the unary restriction of a function of Cobham's class. -/
theorem polyTimeFun_iff_cobhamFun {F : List Bool → List Bool} : PolyTimeFun F ↔ CobhamFun F :=
  cobhamFun_iff_tm2ComputableInPolyTime.symm

theorem PolyTimeFun.cobhamFun {F : List Bool → List Bool} (hF : PolyTimeFun F) : CobhamFun F :=
  polyTimeFun_iff_cobhamFun.1 hF

theorem CobhamFun.polyTimeFun {F : List Bool → List Bool} (hF : CobhamFun F) : PolyTimeFun F :=
  polyTimeFun_iff_cobhamFun.2 hF

/-- A polynomial-time function is the unary restriction of a function of Cobham's class. -/
theorem PolyTimeFun.cobham {F : List Bool → List Bool} (hF : PolyTimeFun F) :
    ∃ f : Fn, Cobham f ∧ ∀ x, F x = f [x] :=
  hF.cobhamFun

/-- The unary restriction of a function of Cobham's class is polynomial time.  This is how
concrete functions are shown to be polynomial time. -/
theorem PolyTimeFun.of_cobham {F : List Bool → List Bool} {f : Fn} (hf : Cobham f)
    (hF : ∀ x, F x = f [x]) : PolyTimeFun F :=
  CobhamFun.polyTimeFun ⟨f, hf, hF⟩

/-- A polynomial-time function is computable. -/
theorem PolyTimeFun.computable {F : List Bool → List Bool} (hF : PolyTimeFun F) :
    Computable F :=
  hF.cobhamFun.computable

/-- A polynomial-time function has polynomially bounded output length. -/
theorem PolyTimeFun.poly_length {F : List Bool → List Bool} (hF : PolyTimeFun F) :
    ∃ p : Polynomial ℕ, ∀ x, (F x).length ≤ p.eval x.length :=
  hF.cobhamFun.poly_length

/-- The identity is polynomial time (directly by Mathlib's identity machine). -/
theorem polyTimeFun_id : PolyTimeFun _root_.id :=
  ⟨idComputableInPolyTime finEncodingListBool⟩

/-- Polynomial time is closed under composition. -/
theorem PolyTimeFun.comp {F G : List Bool → List Bool} (hF : PolyTimeFun F)
    (hG : PolyTimeFun G) : PolyTimeFun (fun x => F (G x)) :=
  (hF.cobhamFun.comp hG.cobhamFun).polyTimeFun

/-- The tail function is polynomial time. -/
theorem polyTimeFun_tail : PolyTimeFun (fun x : List Bool => x.tail) :=
  cobhamFun_tail.polyTimeFun

/-- Appending a fixed string on the right is polynomial time. -/
theorem polyTimeFun_appendConst (y : List Bool) : PolyTimeFun (fun x : List Bool => x ++ y) :=
  (cobhamFun_appendConst y).polyTimeFun

/-! ### Glue: encodings over a binary alphabet -/

section Glue

variable {α β : Type}

/-- **From polynomial time on bit strings to polynomial time on encoded objects.**  If a
polynomial-time function on bit strings maps the (binary) code of every `a` to the code of
`f a`, then `f` is computable in polynomial time with respect to the encodings; the machine is
the one computing the bit-string function. -/
noncomputable def tm2ComputableInPolyTime_of_polyTimeFun (ea : FinEncoding α)
    (eb : FinEncoding β) (ia : ea.Γ ≃ Bool) (ib : eb.Γ ≃ Bool) {f : α → β}
    {F : List Bool → List Bool}
    (hF : TM2ComputableInPolyTime finEncodingListBool finEncodingListBool F)
    (hFf : ∀ a, F ((ea.encode a).map ia) = (eb.encode (f a)).map ib) :
    TM2ComputableInPolyTime ea eb f where
  tm := hF.tm
  inputAlphabet := hF.inputAlphabet.trans ia.symm
  outputAlphabet := hF.outputAlphabet.trans ib.symm
  time := hF.time
  outputsFun a := by
    have h := hF.outputsFun ((ea.encode a).map ia)
    change TM2OutputsInTime hF.tm (List.map hF.inputAlphabet.invFun ((ea.encode a).map ia))
      (some (List.map hF.outputAlphabet.invFun (F ((ea.encode a).map ia))))
      (hF.time.eval ((ea.encode a).map ia).length) at h
    rw [hFf a, List.map_map, List.map_map, List.length_map] at h
    exact h

/-- **From polynomial time on encoded objects to polynomial time on bit strings.**  If `f` is
computable in polynomial time with respect to encodings over binary alphabets, then some
polynomial-time function on bit strings maps the code of every `a` to the code of `f a`.  The
bit-string function is the clocked simulation of the machine: it is defined (and polynomial
time) on all bit strings, and correct on codes. -/
theorem exists_polyTimeFun_of_tm2ComputableInPolyTime (ea : FinEncoding α) (eb : FinEncoding β)
    (ia : ea.Γ ≃ Bool) (ib : eb.Γ ≃ Bool) {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    ∃ F : List Bool → List Bool, PolyTimeFun F ∧
      ∀ a, F ((ea.encode a).map ia) = (eb.encode (f a)).map ib := by
  classical
  set S : List Bool → Prop := fun x => ∃ a, (ea.encode a).map ia = x with hS
  set g : List Bool → List Bool := fun x =>
    if hx : S x then (eb.encode (f hx.choose)).map ib else [] with hg
  have hcode : ∀ a a', (ea.encode a').map ia = (ea.encode a).map ia → a' = a := fun a a' he =>
    ea.encode_injective (List.map_injective_iff.2 ia.injective he)
  have hga : ∀ a, g ((ea.encode a).map ia) = (eb.encode (f a)).map ib := by
    intro a
    have hx : S ((ea.encode a).map ia) := ⟨a, rfl⟩
    simp only [hg, dif_pos hx]
    rw [hcode a _ hx.choose_spec]
  obtain ⟨G, hG, hgG⟩ := exists_cobham_of_outputsOn h.tm (h.inputAlphabet.trans ia)
    (h.outputAlphabet.trans ib) h.time S g (by
      intro x hx
      rw [← hx.choose_spec]
      have ho := h.outputsFun hx.choose
      rw [hga, List.length_map, List.map_map, List.map_map]
      convert ho using 3 <;> ext <;> simp)
  exact ⟨fun x => G [x], PolyTimeFun.of_cobham hG fun _ => rfl, fun a =>
    (hgG _ ⟨a, rfl⟩).symm.trans (hga a)⟩

/-- **Glue theorem.**  For encodings over binary alphabets, polynomial-time computability in the
sense of Mathlib *with respect to these encodings* is equivalent to the existence of a
polynomial-time function on bit strings (`PolyTimeFun`) mapping codes to codes. -/
theorem tm2ComputableInPolyTime_iff (ea : FinEncoding α) (eb : FinEncoding β)
    (ia : ea.Γ ≃ Bool) (ib : eb.Γ ≃ Bool) (f : α → β) :
    Nonempty (TM2ComputableInPolyTime ea eb f) ↔
      ∃ F : List Bool → List Bool, PolyTimeFun F ∧
        ∀ a, F ((ea.encode a).map ia) = (eb.encode (f a)).map ib :=
  ⟨fun ⟨h⟩ => exists_polyTimeFun_of_tm2ComputableInPolyTime ea eb ia ib h,
    fun ⟨_, ⟨hF⟩, hFf⟩ => ⟨tm2ComputableInPolyTime_of_polyTimeFun ea eb ia ib hF hFf⟩⟩

/-- **The Mathlib encoding defined by an injective bit coding.**  The alphabet is `Bool`, the
encoding is `code`, and decoding returns the (unique) object with the given code, if any. -/
noncomputable def finEncodingOfBits (code : α → List Bool) (hinj : Function.Injective code) :
    FinEncoding α where
  Γ := Bool
  encode := code
  decode w := by
    classical
    exact if h : ∃ a, code a = w then some h.choose else none
  decode_encode a := by
    classical
    have h : ∃ a', code a' = code a := ⟨a, rfl⟩
    simp only [dif_pos h]
    exact congrArg some (hinj h.choose_spec)
  ΓFin := inferInstanceAs (Fintype Bool)

@[simp] theorem finEncodingOfBits_encode (code : α → List Bool) (hinj : Function.Injective code) :
    (finEncodingOfBits code hinj).encode = code := rfl

/-- **Glue theorem for bit codings.**  With respect to the encodings defined by injective bit
codings, `f` is computable in polynomial time by a Turing machine iff some polynomial-time
function on bit strings maps the code of every `a` to the code of `f a`. -/
theorem tm2ComputableInPolyTime_bits_iff (ca : α → List Bool) (ha : Function.Injective ca)
    (cb : β → List Bool) (hb : Function.Injective cb) (f : α → β) :
    Nonempty (TM2ComputableInPolyTime (finEncodingOfBits ca ha) (finEncodingOfBits cb hb) f) ↔
      ∃ F : List Bool → List Bool, PolyTimeFun F ∧ ∀ a, F (ca a) = cb (f a) := by
  rw [tm2ComputableInPolyTime_iff _ _ (Equiv.refl Bool) (Equiv.refl Bool)]
  have hm : ∀ l : List Bool, l.map (Equiv.refl Bool) = l := fun l => by simp
  exact exists_congr fun F => and_congr_right fun _ => forall_congr' fun a => by
    show F (List.map (Equiv.refl Bool) (ca a)) = List.map (Equiv.refl Bool) (cb (f a)) ↔ _
    rw [hm, hm]

end Glue

end HTN.PTime
