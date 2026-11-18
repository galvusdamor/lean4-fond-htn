import HtnComplexity.Computable.TokSource
/-!
# The token gadget: the derivations of the compiled description

The compiled description of `HtnComplexity/Computable/TokDom.lean` is totally ordered and
regular, so by the normal form theorem `HTN.Problem.solvable_iff_derives` its solvability is
decided by its *derivations*: chains of methods, each continuing the compound task left open by
the previous one.

This file computes those chains.  Starting from the compiled compound task `ctName c` a
derivation

* picks a source method `i` decomposing `c` and runs `strtA i`,
* then walks the chain `qName i 0, …, qName i n` of counting tasks, running one `doA (i,x)` per
  step (`HTN.Syn.derives_qName`),
* runs `finA i` and continues with the compound task the source method leaves open, if any.

The two shape theorems are `HTN.Syn.derives_qName` and `HTN.Syn.derives_ctName`.
-/

namespace HTN

namespace Syn

open TaskNetwork

variable {d : DomDesc} {q : InstDesc}

/-! ### The bodies of the compiled methods -/

theorem hasBody_body2 (cc a c : ℕ) :
    (MethodDesc.toMethod (cc, body2 a c)).HasBody [a] (some c) := by
  have hids : chainIds [0] (some (1, c)) = ([0, 1] : List ℕ) := by simp
  have h0 : ([0, 1] : List ℕ).idxOf 0 = 0 := by decide
  have h1 : ([0, 1] : List ℕ).idxOf 1 = 1 := by decide
  refine ⟨[0], some (1, c), ⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · rw [hids]; decide
  · intro x
    rw [hids, show (MethodDesc.toMethod (cc, body2 a c)).subtasks = (body2 a c).toTaskNetwork
      from rfl, body2_T]
    simp
  · rfl
  · rintro p ⟨rfl⟩
    rfl
  · intro x y
    rw [hids, show (MethodDesc.toMethod (cc, body2 a c)).subtasks = (body2 a c).toTaskNetwork
      from rfl, body2_ord]
    constructor
    · rintro ⟨rfl, rfl⟩
      refine ⟨by simp, by simp, ?_⟩
      rw [h0, h1]
      omega
    · rintro ⟨hx, hy, hlt⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rw [h0] at hlt; omega
      · exact ⟨rfl, rfl⟩
      · rw [h0, h1] at hlt; omega
      · rw [h1] at hlt; omega

theorem hasBody_body1 (cc a : ℕ) : (MethodDesc.toMethod (cc, body1 a)).HasBody [a] none := by
  refine ⟨[0], none, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · simp
  · intro x
    rw [show (MethodDesc.toMethod (cc, body1 a)).subtasks = (body1 a).toTaskNetwork from rfl,
      body1_T]
    simp
  · rfl
  · rintro p ⟨⟩
  · intro x y
    rw [show (MethodDesc.toMethod (cc, body1 a)).subtasks = (body1 a).toTaskNetwork from rfl]
    constructor
    · intro h
      exact absurd h (body1_ord a x y)
    · rintro ⟨hx, hy, hlt⟩
      simp only [chainIds_none, List.mem_singleton] at hx hy
      subst hx; subst hy
      omega

/-- The body of the compiled method closing the block of the method number `i`. -/
theorem hasBody_finBody (d : DomDesc) (i : ℕ) :
    (MethodDesc.toMethod (qName i (pOf d i).length, finBody d i)).HasBody [finA i]
      ((TnDesc.tailName (tOf d i)).map ctName) := by
  rcases h : TnDesc.hasNextB (tOf d i) with _ | _
  · have hb : finBody d i = body1 (finA i) := by simp [finBody, h]
    rw [hb, TnDesc.tailName, h]
    simpa using hasBody_body1 (qName i (pOf d i).length) (finA i)
  · have hb : finBody d i = body2 (finA i) (ctName (TnDesc.nextName (tOf d i))) := by
      simp [finBody, h]
    rw [hb, TnDesc.tailName, h]
    simpa using hasBody_body2 (qName i (pOf d i).length) (finA i)
      (ctName (TnDesc.nextName (tOf d i)))

/-! ### The methods of the compiled description -/

theorem mem_methods_tok {i : ℕ} (hi : i < d.methods.length) {e : MethodDesc}
    (he : e ∈ tokMethodsOf d i) : e.toMethod ∈ (problem (tokDom d) q).methods :=
  ⟨e, mem_tokMethods_iff.2 ⟨i, hi, he⟩, rfl⟩

theorem mem_methods_entry {i : ℕ} (hi : i < d.methods.length) :
    MethodDesc.toMethod (ctName (cOf d i), body2 (strtA i) (qName i 0)) ∈
      (problem (tokDom d) q).methods :=
  mem_methods_tok hi (by simp [tokMethodsOf])

theorem mem_methods_step {i k x : ℕ} (hi : i < d.methods.length) (hk : k < (pOf d i).length)
    (hx : x ∈ pOf d i) :
    MethodDesc.toMethod (qName i k, body2 (doA i x) (qName i (k + 1))) ∈
      (problem (tokDom d) q).methods := by
  refine mem_methods_tok hi ?_
  simp only [tokMethodsOf, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_range]
  exact Or.inl (Or.inr ⟨k, hk, x, hx, rfl⟩)

theorem mem_methods_fin {i : ℕ} (hi : i < d.methods.length) :
    MethodDesc.toMethod (qName i (pOf d i).length, finBody d i) ∈
      (problem (tokDom d) q).methods := by
  exact mem_methods_tok hi (by simp [tokMethodsOf])

theorem methods_classify {m : Method ℕ ℕ ℕ} (hm : m ∈ (problem (tokDom d) q).methods) :
    ∃ i, i < d.methods.length ∧
      (m = MethodDesc.toMethod (ctName (cOf d i), body2 (strtA i) (qName i 0)) ∨
        (∃ k, k < (pOf d i).length ∧ ∃ x ∈ pOf d i,
          m = MethodDesc.toMethod (qName i k, body2 (doA i x) (qName i (k + 1)))) ∨
        m = MethodDesc.toMethod (qName i (pOf d i).length, finBody d i)) := by
  obtain ⟨e, he, rfl⟩ := hm
  obtain ⟨i, hi, hie⟩ := mem_tokMethods_iff.1 he
  refine ⟨i, hi, ?_⟩
  simp only [tokMethodsOf, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_range] at hie
  rcases hie with (rfl | ⟨k, hk, x, hx, rfl⟩) | (rfl | hnil)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨k, hk, x, hx, rfl⟩)
  · exact Or.inr (Or.inr rfl)
  · simp at hnil

/-- A method of the compiled description whose compound task is a counting task is a step
method or the closing method. -/
theorem methods_classify_qName {m : Method ℕ ℕ ℕ} (hm : m ∈ (problem (tokDom d) q).methods)
    {i k : ℕ} (hi : i < d.methods.length) (hab : m.abstractTask = qName i k) :
    (k < (pOf d i).length ∧ ∃ x ∈ pOf d i,
        m = MethodDesc.toMethod (qName i k, body2 (doA i x) (qName i (k + 1)))) ∨
      (k = (pOf d i).length ∧ m = MethodDesc.toMethod (qName i (pOf d i).length, finBody d i)) := by
  obtain ⟨j, hj, hcase⟩ := methods_classify hm
  rcases hcase with rfl | ⟨k', hk', x, hx, rfl⟩ | rfl
  · exact absurd hab ctName_ne_qName
  · have h : qName j k' = qName i k := hab
    obtain ⟨rfl, rfl⟩ := qName_inj.1 h
    exact Or.inl ⟨hk', x, hx, rfl⟩
  · have h : qName j (pOf d j).length = qName i k := hab
    obtain ⟨rfl, rfl⟩ := qName_inj.1 h
    exact Or.inr ⟨rfl, rfl⟩

/-- A method of the compiled description whose compound task is a compiled source task is an
entry method. -/
theorem methods_classify_ctName {m : Method ℕ ℕ ℕ} (hm : m ∈ (problem (tokDom d) q).methods)
    {c : ℕ} (hab : m.abstractTask = ctName c) :
    ∃ i, i < d.methods.length ∧ cOf d i = c ∧
      m = MethodDesc.toMethod (ctName (cOf d i), body2 (strtA i) (qName i 0)) := by
  obtain ⟨j, hj, hcase⟩ := methods_classify hm
  rcases hcase with rfl | ⟨k', hk', x, hx, rfl⟩ | rfl
  · exact ⟨j, hj, ctName_inj.1 hab, rfl⟩
  · exact absurd hab.symm ctName_ne_qName
  · exact absurd hab.symm ctName_ne_qName

/-! ### The shape of a derivation of the compiled description -/

/-- What a derivation of the compiled description does after the block of the method number
`i`: it continues with the compound task the source method leaves open, or stops. -/
def TailDer (d : DomDesc) (q : InstDesc) (i : ℕ) (rest : List ℕ) : Prop :=
  match TnDesc.tailName (tOf d i) with
  | none => rest = []
  | some c' => (problem (tokDom d) q).Derives (ctName c') rest

/-- **The chain of counting tasks.**  A derivation of `qName i k` runs `(pOf d i).length - k`
of the compiled subtask actions of the method `i`, then closes the block. -/
theorem derives_qName {i : ℕ} (hi : i < d.methods.length) :
    ∀ (r k : ℕ), k + r = (pOf d i).length → ∀ bs : List ℕ,
      (problem (tokDom d) q).Derives (qName i k) bs ↔
        ∃ (xs : List ℕ) (rest : List ℕ), xs.length = r ∧ (∀ x ∈ xs, x ∈ pOf d i) ∧
          bs = xs.map (doA i) ++ finA i :: rest ∧ TailDer d q i rest := by
  intro r
  induction r with
  | zero =>
      intro k hk bs
      simp only [Nat.add_zero] at hk
      subst hk
      constructor
      · intro hder
        cases hder with
        | @last c os m hm hc hb =>
            rcases methods_classify_qName hm hi hc with ⟨hlt, -⟩ | ⟨-, rfl⟩
            · exact absurd hlt (by omega)
            · have huniq := Method.HasBody.unique hb (hasBody_finBody d i)
              rcases htail : TnDesc.tailName (tOf d i) with _ | c'
              · refine ⟨[], [], rfl, by simp, ?_, ?_⟩
                · simpa using huniq.1
                · simp [TailDer, htail]
              · rw [htail] at huniq
                exact absurd huniq.2 (by simp)
        | @cons c c' os rest m hm hc hb hrest =>
            rcases methods_classify_qName hm hi hc with ⟨hlt, -⟩ | ⟨-, rfl⟩
            · exact absurd hlt (by omega)
            · have huniq := Method.HasBody.unique hb (hasBody_finBody d i)
              rcases htail : TnDesc.tailName (tOf d i) with _ | c''
              · rw [htail] at huniq
                exact absurd huniq.2 (by simp)
              · rw [htail] at huniq
                have hos : os = [finA i] := huniq.1
                have hc'' : ctName c'' = c' := by simpa using huniq.2.symm
                refine ⟨[], rest, rfl, by simp, by simp [hos], ?_⟩
                simp only [TailDer, htail]
                rw [hc'']
                exact hrest
      · rintro ⟨xs, rest, hlen, -, rfl, htail⟩
        have hxs : xs = [] := List.eq_nil_of_length_eq_zero hlen
        subst hxs
        simp only [List.map_nil, List.nil_append]
        have hb := hasBody_finBody d i
        rcases htaileq : TnDesc.tailName (tOf d i) with _ | c'
        · have hrest : rest = [] := by simpa [TailDer, htaileq] using htail
          subst hrest
          rw [htaileq] at hb
          exact Problem.Derives.last (mem_methods_fin hi) rfl (by simpa using hb)
        · have hd : (problem (tokDom d) q).Derives (ctName c') rest := by
            simpa [TailDer, htaileq] using htail
          rw [htaileq] at hb
          have := Problem.Derives.cons (mem_methods_fin hi) rfl (by simpa using hb) hd
          simpa using this
  | succ r ih =>
      intro k hk bs
      constructor
      · intro hder
        cases hder with
        | @last c os m hm hc hb =>
            rcases methods_classify_qName hm hi hc with ⟨hlt, x, hx, rfl⟩ | ⟨hne, -⟩
            · have huniq := Method.HasBody.unique hb
                (hasBody_body2 (qName i k) (doA i x) (qName i (k + 1)))
              exact absurd huniq.2 (by simp)
            · omega
        | @cons c c' os rest m hm hc hb hrest =>
            rcases methods_classify_qName hm hi hc with ⟨hlt, x, hx, rfl⟩ | ⟨hne, -⟩
            · have huniq := Method.HasBody.unique hb
                (hasBody_body2 (qName i k) (doA i x) (qName i (k + 1)))
              have hos : os = [doA i x] := huniq.1
              have hc' : c' = qName i (k + 1) := by simpa using huniq.2
              subst hc'
              obtain ⟨xs, rest', hlen, hmem, rfl, htail⟩ :=
                (ih (k + 1) (by omega) rest).1 hrest
              refine ⟨x :: xs, rest', by simp [hlen], ?_, by simp [hos], htail⟩
              intro y hy
              rcases List.mem_cons.1 hy with rfl | hy
              · exact hx
              · exact hmem y hy
            · omega
      · rintro ⟨xs, rest, hlen, hmem, rfl, htail⟩
        obtain ⟨x, xs', rfl⟩ : ∃ x xs', xs = x :: xs' := by
          cases xs with
          | nil => simp at hlen
          | cons x xs' => exact ⟨x, xs', rfl⟩
        have hx : x ∈ pOf d i := hmem x (by simp)
        have hlt : k < (pOf d i).length := by omega
        have hrest : (problem (tokDom d) q).Derives (qName i (k + 1))
            (xs'.map (doA i) ++ finA i :: rest) :=
          (ih (k + 1) (by omega) _).2 ⟨xs', rest, by simpa using hlen, fun y hy =>
            hmem y (by simp [hy]), rfl, htail⟩
        have := Problem.Derives.cons (P := problem (tokDom d) q)
          (mem_methods_step hi hlt hx) rfl
          (hasBody_body2 (qName i k) (doA i x) (qName i (k + 1))) hrest
        simpa using this

/-- **The derivations of the compiled description.**  A derivation of the compiled compound
task `ctName c` picks a source method decomposing `c`, runs its start action, one compiled
action per primitive subtask, its closing action, and continues with the compound task the
source method leaves open. -/
theorem derives_ctName {c : ℕ} {bs : List ℕ} :
    (problem (tokDom d) q).Derives (ctName c) bs ↔
      ∃ i, i < d.methods.length ∧ cOf d i = c ∧ ∃ (xs : List ℕ) (rest : List ℕ),
        xs.length = (pOf d i).length ∧ (∀ x ∈ xs, x ∈ pOf d i) ∧
        bs = strtA i :: (xs.map (doA i) ++ finA i :: rest) ∧ TailDer d q i rest := by
  constructor
  · intro hder
    cases hder with
    | @last c' os m hm hc hb =>
        obtain ⟨i, hi, hci, rfl⟩ := methods_classify_ctName hm hc
        have huniq := Method.HasBody.unique hb
          (hasBody_body2 (ctName (cOf d i)) (strtA i) (qName i 0))
        exact absurd huniq.2 (by simp)
    | @cons c' c'' os rest m hm hc hb hrest =>
        obtain ⟨i, hi, hci, rfl⟩ := methods_classify_ctName hm hc
        have huniq := Method.HasBody.unique hb
          (hasBody_body2 (ctName (cOf d i)) (strtA i) (qName i 0))
        have hos : os = [strtA i] := huniq.1
        have hc'' : c'' = qName i 0 := by simpa using huniq.2
        subst hc''
        obtain ⟨xs, rest', hlen, hmem, rfl, htail⟩ :=
          (derives_qName hi (pOf d i).length 0 (by omega) rest).1 hrest
        exact ⟨i, hi, hci, xs, rest', hlen, hmem, by simp [hos], htail⟩
  · rintro ⟨i, hi, rfl, xs, rest, hlen, hmem, rfl, htail⟩
    have hrest := (derives_qName hi (pOf d i).length 0 (by omega)
      (xs.map (doA i) ++ finA i :: rest)).2 ⟨xs, rest, hlen, hmem, rfl, htail⟩
    have := Problem.Derives.cons (mem_methods_entry hi) rfl
      (hasBody_body2 (ctName (cOf d i)) (strtA i) (qName i 0)) hrest
    simpa using this

end Syn

end HTN
