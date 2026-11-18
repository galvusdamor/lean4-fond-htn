import HtnComplexity.AcVerify.AdvSize
import HtnComplexity.AcVerify.VerCobham
import HtnComplexity.Space.InstBound
import HtnComplexity.Hypotheses.ExpSpace
import HtnPlanning.Computable.PermFix
import HtnPlanning.Computable.Rename
/-!
# `HTN-AC` is in `NEXPTIME` (with the domain as advice)

**`HTN.Syn.AcVer.nExpDecidableAdv_HTN_AC`** — the target interface
`HTN.Syn.NExpDecidableAdv codingSer SynClass.HTN_AC` of the cell (`HTN-TR`, `HTN-AC`), with no
hypothesis left.

* the verifier is `HTN.Syn.AcVer.acV`, a predicate of Cobham's class
  (`HTN.Syn.AcVer.cobhamB_acV`) — it does not depend on the family of domains;
* for each `n` the domain description `D n` is first **renamed** by a permutation of `ℕ` that fixes
  every number below `2 ^ rq(n)` (hence every name of every instance description of code length
  at most `rq(n)`) and moves the names of `D n` into numbers below `2 ^ (rq(n) + 2 r(n) + 1)`
  (`HTN.exists_perm_fixing`); renaming does not change solvability
  (`HTN.Syn.solvable_rename_iff`), acyclicity or size;
* the advice is the table form `advOf` of the renamed domain, of polynomial length
  (`HTN.Syn.AcVer.length_advOf_le`);
* `Solvable ↔ ∃ accepted certificate` (`HTN.Syn.AcVer.solvable_iff_exists_acV`), and an accepted
  certificate can be chosen of length at most `2 ^ p(n)` because the domain is acyclic
  (`HTN.Syn.AcVer.length_certOf_le`, `HTN.Syn.AcVer.certBound_le`).
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

/-! ### Small numbers in an instance description -/

theorem length_bitsOfNat_le_of_mem_names {q : InstDesc} {x : ℕ} (hx : x ∈ q.names) :
    (bitsOfNat x).length ≤ (instSer q).length := by
  have hinst : (instSer q).length = (serNatList q.initList).length +
      (serNatList q.goalList).length + ((serNatList q.tnI.ids).length +
        (serPairList q.tnI.ordList).length + (serLblList q.tnI.lbl).length) := by
    simp [instSer, tnSer]; omega
  unfold InstDesc.names TnDesc.names at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · have := two_length_bitsOfNat_le_serNatList hx; omega
    · have := two_length_bitsOfNat_le_serNatList hx; omega
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · have := two_length_bitsOfNat_le_serNatList hx; omega
    obtain ⟨p, hp, h⟩ := List.mem_flatMap.1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have h1 := le_length_blist_of_mem (List.mem_map_of_mem (f := serPair) hp)
    rw [← serPairList] at h1
    have h2 : (serPair p).length = 2 * (bitsOfNat p.1).length + 1 +
        (2 * (bitsOfNat p.2).length + 1) := by simp [serPair, serNat]
    rcases h with rfl | rfl <;> omega
  · obtain ⟨l, hl, h⟩ := List.mem_flatMap.1 hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have h1 := le_length_blist_of_mem (List.mem_map_of_mem (f := serLbl) hl)
    rw [← serLblList] at h1
    have h2 : (serLbl l).length = 2 * (bitsOfNat l.1).length + 1 + 1 +
        (2 * (bitsOfNat l.2.2).length + 1) := by simp [serLbl, serNat]; omega
    rcases h with rfl | rfl <;> omega

theorem lt_of_mem_names {q : InstDesc} {x L : ℕ} (hq : (instSer q).length ≤ L)
    (hx : x ∈ q.names) : x < 2 ^ L :=
  lt_two_pow_of_length_bitsOfNat_le ((length_bitsOfNat_le_of_mem_names hx).trans hq)

/-! ### Renaming preserves acyclicity -/

theorem isAcyclic_rename {d : DomDesc} (hd : d.IsAcyclic) (π : Equiv.Perm ℕ) (h0 : π 0 = 0) :
    (d.rename π).IsAcyclic := by
  obtain ⟨rk, hrk⟩ := hd
  refine ⟨fun c => rk (π.symm c), ?_⟩
  intro e' he' t ht c hc
  simp only [DomDesc.rename_methods, List.mem_map] at he'
  obtain ⟨e, he, rfl⟩ := he'
  simp only [MethodDesc.rename, TnDesc.toTaskNetwork, List.mem_toFinset,
    TnDesc.rename_ids, List.mem_map] at ht hc ⊢
  obtain ⟨t0, ht0, rfl⟩ := ht
  rw [label_rename π.injective h0] at hc
  rcases hl : e.2.label t0 with a | c0
  · rw [hl] at hc; simp at hc
  · rw [hl] at hc
    simp only [Sum.map_inr, Sum.inr.injEq] at hc
    subst hc
    simp only [Equiv.symm_apply_apply]
    exact hrk e he t0 (by simpa [TnDesc.toTaskNetwork] using ht0) c0
      (by simpa [TnDesc.toTaskNetwork] using hl)

/-! ### The renaming of a family of domains -/

theorem foldr_max_le {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) : l.foldr max 0 ≤ M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- The permutation renaming the domain description `d`: it fixes the numbers below `2 ^ L` and
moves the names of `d` into the numbers below `2 ^ L + k + 1`, for `k ≥ 2 · |d|`. -/
theorem exists_perm_small (d : DomDesc) (L k : ℕ) (hk : 2 * d.size ≤ k) :
    ∃ π : Equiv.Perm ℕ, (∀ x < 2 ^ L, π x = x) ∧ ∀ y ∈ d.names, π y < 2 ^ L + k + 1 := by
  set S := List.range (2 ^ L)
  obtain ⟨π, hfix, hmap⟩ := exists_perm_fixing S (freshBlock S k) (freshBlock_nodup S k)
    (freshBlock_notMem S k) d.names (by rw [length_freshBlock]; exact (d.length_names_le).trans hk)
  refine ⟨π, fun x hx => hfix x (List.mem_range.2 hx), fun y hy => ?_⟩
  rcases List.mem_append.1 (hmap y hy) with h | h
  · have := List.mem_range.1 h; omega
  · obtain ⟨i, hi, he⟩ := List.mem_map.1 h
    rw [← he]
    have := List.mem_range.1 hi
    have : S.foldr max 0 ≤ 2 ^ L := foldr_max_le fun x hx => (List.mem_range.1 hx).le
    omega

/-- The renamed domain description. -/
noncomputable def renDom (d : DomDesc) (L k : ℕ) : DomDesc :=
  if hk : 2 * d.size ≤ k then d.rename (exists_perm_small d L k hk).choose else d

theorem renDom_spec (d : DomDesc) (L k : ℕ) (hk : 2 * d.size ≤ k) :
    ∃ π : Equiv.Perm ℕ, (∀ x < 2 ^ L, π x = x) ∧ (∀ y ∈ d.names, π y < 2 ^ L + k + 1) ∧
      renDom d L k = d.rename π :=
  ⟨_, (exists_perm_small d L k hk).choose_spec.1, (exists_perm_small d L k hk).choose_spec.2,
    by simp [renDom, hk]⟩

theorem two_pow_add_lt {L k : ℕ} : 2 ^ L + k + 1 ≤ 2 ^ (L + k + 1) := by
  have h1 : k + 2 ≤ 2 ^ (k + 1) := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  rw [show L + k + 1 = L + (k + 1) by ring, pow_add]
  nlinarith [Nat.mul_le_mul_left (2 ^ L) h1, Nat.mul_le_mul_right k h2]

/-- **The properties of the renamed domain.** -/
theorem renDom_props {d : DomDesc} (hd : d.IsAcyclic) {L k : ℕ} (hk : 2 * d.size ≤ k) :
    (renDom d L k).IsAcyclic ∧ (renDom d L k).size = d.size ∧
      DomNamesLt (renDom d L k) (L + k + 1) ∧
      ∀ q : InstDesc, (instSer q).length ≤ L → (Solvable (renDom d L k) q ↔ Solvable d q) := by
  obtain ⟨π, hfix, hmap, heq⟩ := renDom_spec d L k hk
  have h0 : π 0 = 0 := hfix 0 (Nat.one_le_two_pow)
  rw [heq]
  refine ⟨isAcyclic_rename hd π h0, DomDesc.size_rename _ _, ⟨?_, ?_⟩, fun q hq => ?_⟩
  · intro x hx
    rw [DomDesc.names_rename] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (hmap y hy).trans_le two_pow_add_lt
  · have h1 := length_methods_le d
    have h2 : d.methods.length + 1 < 2 ^ (k + 1) := by
      have := (Nat.lt_two_pow_self (n := k + 1)); omega
    simp only [DomDesc.rename_methods, List.length_map]
    exact h2.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  · have hqe : q.rename π = q :=
      InstDesc.rename_eq_self fun x hx => hfix x (lt_of_mem_names hq hx)
    have := solvable_rename_iff π.injective h0 d q
    rwa [hqe] at this

/-! ### The theorem -/

/-- The bound on the bit length of the renamed names. -/
noncomputable def bitsP (r rq : Polynomial ℕ) : Polynomial ℕ := rq + 2 * r + 1

/-- The exponent of the certificate bound. -/
noncomputable def expP (r rq : Polynomial ℕ) : Polynomial ℕ :=
  4 * (rq + r + bitsP r rq) * (rq + r + bitsP r rq) + 8 * (rq + r + bitsP r rq) + 16

/-- The bound on the advice. -/
noncomputable def advP (r rq : Polynomial ℕ) : Polynomial ℕ :=
  5 * (1 + (r + 1) ^ 2 * (2 * (3 * (1 + r * (2 * bitsP r rq + 2)) + 8 * bitsP r rq + 4) + 2))

/-- **`HTN-AC` is in `NEXPTIME`, the domain description being supplied as advice.** -/
theorem nExpDecidableAdv_HTN_AC : NExpDecidableAdv codingSer SynClass.HTN_AC := by
  intro D r rq hok hsize
  set L : ℕ → ℕ := fun n => rq.eval n
  set k : ℕ → ℕ := fun n => 2 * r.eval n
  have hk : ∀ n, 2 * (D n).size ≤ k n := fun n => by have := hsize n; simp only [k]; omega
  refine ⟨acV, expP r rq, advP r rq, fun n => advOf (renDom (D n) (L n) (k n)), cobhamB_acV,
    fun n => ?_, fun n q _ hq => ?_⟩
  · obtain ⟨-, hsz, hB, -⟩ := renDom_props (hok n) (hk n)
    refine (length_advOf_le hB).trans ?_
    rw [hsz]
    refine (advBound_mono (hsize n) le_rfl).trans (le_of_eq ?_)
    simp [advBound, rowBound, advP, bitsP, L, k]
  · obtain ⟨hac, hsz, hB, hsol⟩ := renDom_props (hok n) (hk n) (L := L n)
    have hq' : (instSer q).length ≤ L n := hq
    constructor
    · intro hs
      obtain ⟨W, hW, h0⟩ := exists_pathOK0_of_solvable ((hsol q hq').2 hs)
      refine ⟨_, ?_, acV_certOf hW h0⟩
      set X := rq.eval n + r.eval n + (L n + k n + 1)
      have hN : NamesLt (renDom (D n) (L n) (k n)) q (L n + k n + 1) :=
        ⟨hB.dom, fun x hx => (lt_of_mem_names hq' hx).trans_le
          (Nat.pow_le_pow_right (by omega) (by omega)), hB.meth⟩
      refine (length_certOf_le hac hN hW h0).trans ?_
      have hqs : q.size ≤ X := (size_le_length_instSer q).trans (by simp only [X, L] at hq' ⊢; omega)
      have hds : (renDom (D n) (L n) (k n)).size ≤ X := by
        rw [hsz]; have := hsize n; simp only [X]; omega
      refine (certBound_mono hqs hds (by simp only [X]; omega)).trans
        ((certBound_le X).trans (le_of_eq ?_))
      simp [expP, bitsP, X, L, k]
    · rintro ⟨w, -, hw⟩
      exact (hsol q hq').1 (solvable_of_acV hw)

end AcVer

end Syn

end HTN
