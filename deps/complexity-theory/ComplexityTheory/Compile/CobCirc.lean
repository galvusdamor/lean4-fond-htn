import ComplexityTheory.Compile.Smash
import ComplexityTheory.Compile.Brn
/-!
# The circuits of Cobham's class: composition, and the induction

This file completes the induction announced in `ComplexityTheory/Compile/Fam.lean`: the
circuits of the inner functions of a composition are relocated side by side, their outputs
widened to a common bound, and the circuit of the outer function is relocated on top.  With the
base cases of `ComplexityTheory/Compile/Base.lean`, the smash function of
`ComplexityTheory/Compile/Smash.lean` and the bounded recursion of
`ComplexityTheory/Compile/Brn.lean`, every function of Cobham's class has a uniform family of
polynomial-size circuits at every arity (`HTN.Compile.cobham_circFam'`).
-/

namespace HTN

namespace Compile

open PTime
/-! ### Composition -/

/-- **A finite list of functions has circuit families at a common output bound.** -/
theorem circFam_common (k : ℕ) : ∀ hs : List Fn, (∀ h ∈ hs, Nonempty (CircFam h k)) →
    ∃ Bp : Polynomial ℕ, ∀ h ∈ hs, ∃ F : CircFam h k, F.B = Bp := by
  intro hs
  induction hs with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons h hs ih =>
      intro hF
      obtain ⟨Bp, hBp⟩ := ih fun u hu => hF u (by simp [hu])
      obtain ⟨Fh⟩ := hF h (by simp)
      refine ⟨Bp + Fh.B, fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact circFam_widen Fh (Bp + Fh.B) fun n => by simp
      · obtain ⟨G, hG⟩ := hBp u hu
        exact circFam_widen G (Bp + Fh.B) fun n => by rw [hG]; simp

/-- **The circuits of a list of functions, side by side**: one circuit whose outputs are the
cell encoding of the list of values at a common bound. -/
theorem circFam_args (k : ℕ) (Bp : Polynomial ℕ) : ∀ hs : List Fn,
    (∀ h ∈ hs, ∃ F : CircFam h k, F.B = Bp) →
    ∃ (Cs : ℕ → Circ) (bnd : Polynomial ℕ),
      (∀ n, (Cs n).nin = 2 * n * k) ∧ Primrec Cs ∧
      (∀ n, (Cs n).size ≤ bnd.eval n) ∧
      (∀ n, ∀ j ∈ (Cs n).out, j < (Cs n).nin + (Cs n).gates.length) ∧
      (∀ n args, args.length = k → (∀ a ∈ args, a.length ≤ n) →
        (Cs n).eval (encArgs k n args)
          = encArgs hs.length (Bp.eval n) (hs.map fun h => h args)) := by
  intro hs
  induction hs with
  | nil =>
      intro _
      refine ⟨fun n => (2 * n * k, [], []), Polynomial.C (2 * k) * Polynomial.X,
        fun n => rfl, ?_, ?_, fun n j hj => absurd hj (by simp), ?_⟩
      · exact Primrec.pair (primrec_nin_mul k)
          (Primrec.pair (Primrec.const []) (Primrec.const []))
      · intro n
        simp only [Circ.size, Circ.nin_mk, Circ.gates_mk, Circ.out_mk, List.length_nil,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        nlinarith
      · intro n args _ _
        simp [eval_nogates, encArgs]
  | cons h hs ih =>
      intro hF
      obtain ⟨Cs, bnd, hnin, hprim, hsize, hout, hcorr⟩ := ih fun u hu => hF u (by simp [hu])
      obtain ⟨F, hFB⟩ := hF h (by simp)
      refine ⟨fun n => stackCirc (2 * n * k) (F.C n) (Cs n), F.bnd + bnd, fun n => rfl, ?_, ?_,
        ?_, ?_⟩
      · have hb : Primrec fun n : ℕ => 2 * n * k + (F.C n).gates.length :=
          Primrec.nat_add.comp (primrec_nin_mul k) (Primrec.list_length.comp (primrec_gates F))
        have hs' : Primrec fun n : ℕ => List.range (2 * n * k) :=
          Primrec.list_range.comp (primrec_nin_mul k)
        exact Primrec.pair (primrec_nin_mul k)
          (Primrec.pair (Primrec.list_append.comp (primrec_gates F)
              (primrec_relocGates hprim hb hs'))
            (Primrec.list_append.comp (primrec_out F) (primrec_relocOut hprim hb hs')))
      · intro n
        have h1 := F.size_le n
        have h2 := hsize n
        rw [Circ.size, F.nin_eq n] at h1
        rw [Circ.size, hnin n] at h2
        simp only [stackCirc, Circ.size, Circ.nin_mk, Circ.gates_mk, Circ.out_mk,
          List.length_append, length_relocGates, length_relocOut, Polynomial.eval_add]
        omega
      · intro n
        exact stackCirc_out_lt (F.nin_eq n) (hnin n) (F.out_lt n) (hout n)
      · intro n args hargs hlen
        have hinp : (encArgs k n args).length = 2 * n * k := by simp
        rw [stackCirc_eval (F.nin_eq n) (hnin n) hinp (F.out_lt n),
          F.correct n args hargs hlen, hcorr n args hargs hlen, hFB]
        rw [List.length_cons, List.map_cons, encArgs_cons]

theorem circFam_comp {g : Fn} {hs : List Fn} (Fg : CircFam g hs.length)
    (Fh : ∀ h ∈ hs, ∀ k, Nonempty (CircFam h k)) (k : ℕ) :
    Nonempty (CircFam (compFn g hs) k) := by
  obtain ⟨Bp, hBp⟩ := circFam_common k hs fun u hu => Fh u hu k
  obtain ⟨Cs, bnd, hnin, hprim, hsize, hout, hcorr⟩ := circFam_args k Bp hs hBp
  -- the outputs of the side-by-side circuit are the inputs of the outer circuit
  have houtlen : ∀ n, (Cs n).out.length = 2 * Bp.eval n * hs.length := by
    intro n
    have h := hcorr n (List.replicate k []) (by simp) (by
      intro a ha; rw [List.eq_of_mem_replicate ha]; simp)
    have := congrArg List.length h
    rwa [Circ.eval, List.length_map, length_encArgs] at this
  have hlenh : ∀ (n : ℕ) (args : Args), args.length = k → (∀ a ∈ args, a.length ≤ n) →
      ∀ a ∈ hs.map fun u => u args, a.length ≤ Bp.eval n := by
    intro n args hargs hlen a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
    obtain ⟨G, hG⟩ := hBp u hu
    have := G.len_le n args hargs hlen
    rwa [hG] at this
  refine ⟨{
    C := fun n => feedCirc (2 * n * k) (Cs n) (Fg.C (Bp.eval n))
    B := Fg.B.comp Bp
    bnd := bnd + Fg.bnd.comp Bp
    nin_eq := fun n => rfl
    primC := ?_
    size_le := ?_
    out_lt := ?_
    len_le := ?_
    correct := ?_ }⟩
  · have hg : Primrec fun n : ℕ => Fg.C (Bp.eval n) := Fg.primC.comp (primrec_poly_eval Bp)
    have hb : Primrec fun n : ℕ => 2 * n * k + (Cs n).gates.length :=
      Primrec.nat_add.comp (primrec_nin_mul k)
        (Primrec.list_length.comp ((Primrec.fst.comp (Primrec.snd.comp hprim)).of_eq
          fun _ => rfl))
    have hsrc : Primrec fun n : ℕ => (Cs n).out :=
      (Primrec.snd.comp (Primrec.snd.comp hprim)).of_eq fun _ => rfl
    exact Primrec.pair (primrec_nin_mul k)
      (Primrec.pair (Primrec.list_append.comp
          ((Primrec.fst.comp (Primrec.snd.comp hprim)).of_eq fun _ => rfl)
          (primrec_relocGates hg hb hsrc))
        (primrec_relocOut hg hb hsrc))
  · intro n
    have h1 := hsize n
    have h2 := Fg.size_le (Bp.eval n)
    rw [Circ.size, hnin n] at h1
    rw [Circ.size] at h2
    simp only [feedCirc, Circ.size, Circ.nin_mk, Circ.gates_mk, Circ.out_mk,
      List.length_append, length_relocGates, length_relocOut, Polynomial.eval_add,
      Polynomial.eval_comp]
    omega
  · intro n
    exact feedCirc_out_lt (by rw [Fg.nin_eq (Bp.eval n), houtlen n]) (hout n) (hnin n)
      (Fg.out_lt (Bp.eval n))
  · intro n args hargs hlen
    have := Fg.len_le (Bp.eval n) (hs.map fun u => u args) (by simp)
      (hlenh n args hargs hlen)
    rwa [Polynomial.eval_comp]
  · intro n args hargs hlen
    have hinp : (encArgs k n args).length = 2 * n * k := by simp
    rw [feedCirc_eval (hnin n) hinp (by rw [Fg.nin_eq (Bp.eval n), houtlen n]) (hout n),
      hcorr n args hargs hlen,
      Fg.correct (Bp.eval n) (hs.map fun u => u args) (by simp) (hlenh n args hargs hlen),
      Polynomial.eval_comp]
    rfl

/-! ### The induction -/

/-- **Every function of Cobham's class has a uniform circuit family at every arity.** -/
theorem cobham_circFam' {f : Fn} (hf : Cobham f) : ∀ k, Nonempty (CircFam f k) := by
  induction hf with
  | empty => exact circFam_empty
  | proj m => exact circFam_proj m
  | cons b => exact circFam_cons b
  | smash => exact circFam_smash
  | comp _ _ ihg ihs =>
      intro k
      exact (ihg _).elim fun Fg => circFam_comp Fg (fun h hh => ihs h hh) k
  | @brn g h0 h1 bd _ _ _ hbdc hbound ihg ih0 ih1 _ =>
      intro k
      obtain ⟨pbd, hpbd⟩ := hbdc.poly_length
      exact circFam_brn ihg ih0 ih1 hbound pbd hpbd k

end Compile

end HTN
