import HtnComplexity.Logspace.Nav
/-!
# Checking properties of located lists

Quantifiers over the entries of a located list and the usual tests on lists of keys (numbers
at the front of the entries), as terms with their meaning:

* `allE`, `exE` — `∀`/`∃` over the entries (`HTN.Logspace.eval_allE`, `HTN.Logspace.eval_exE`);
  the body sees the index as variable `1` and the entry at `entryT d (lift 2 L) (var 1)`;
* `memKeyT` — a number is a key of the list (`HTN.Logspace.eval_memKeyT`);
* `nodupKeyT` — the keys are distinct (`HTN.Logspace.eval_nodupKeyT`);
* `cntT` — counting (`HTN.Logspace.eval_cntT`).

A **key** of a format is a number written at the front of its values (`HTN.Logspace.Key`).
-/

namespace HTN

namespace Logspace

open Cx Cx.LTerm Syn

variable {y : List Bool} {M : ℕ}

/-- `key a` is written at the front of every location of `a`. -/
def Key (y : List Bool) (d : ℕ) (F : Fmt) (key : F.ty → ℕ) : Prop :=
  ∀ q a, At y d q F a → At y d q .nat (key a)

theorem key_nat (d : ℕ) : Key y d .nat id := fun _ _ h => h

theorem key_fst (d : ℕ) (G : Fmt) : Key y d (.pair .nat G) Prod.fst := fun _ a h => by
  obtain ⟨a, b⟩ := a; exact h.fst

/-- `∀` over the entries of the list at `(d, L)`. -/
def allE (d : ℕ) (L B : LTerm) : LTerm := forallB (lenT d L) B

/-- `∃` over the entries of the list at `(d, L)`. -/
def exE (d : ℕ) (L B : LTerm) : LTerm := existsB (lenT d L) B

section

variable {F : Fmt} {d : ℕ} {L : LTerm} {env : List ℕ} {l : List F.ty}

theorem eval_allE (hM : y.length + 2 ≤ M) (h : At y d (eval y M env L) (.list F) l) (B : LTerm) :
    eval y M env (allE d L B) ≠ 0 ↔ ∀ i < l.length, eval y M (1 :: i :: env) B ≠ 0 := by
  rw [allE, eval_forallB, eval_lenT hM h]
  split_ifs with h'
  · simpa using h'
  · simpa using h'

theorem eval_exE (hM : y.length + 2 ≤ M) (h : At y d (eval y M env L) (.list F) l) (B : LTerm) :
    eval y M env (exE d L B) ≠ 0 ↔ ∃ i < l.length, eval y M (0 :: i :: env) B ≠ 0 := by
  rw [exE, eval_existsB, eval_lenT hM h]
  split_ifs with h'
  · simpa using h'
  · simpa using h'

theorem At.entry2 (hM : y.length + 2 ≤ M) (h : At y d (eval y M env L) (.list F) l) {i : ℕ}
    (hi : i < l.length) (a : ℕ) :
    At y (d + 1) (eval y M (a :: i :: env) (entryT d (lift 2 L) (.var 1))) F l[i] :=
  At.entry hM (by rwa [eval_lift2]) hi (by simp [eval])

theorem At.lift2 {d' : ℕ} {G : Fmt} {X : LTerm} {x : G.ty} (h : At y d' (eval y M env X) G x) (a b : ℕ) :
    At y d' (eval y M (a :: b :: env) (lift 2 X)) G x := by rwa [eval_lift2]

end

/-- **The number at `(dx, X)` is a key of the list at `(d, L)`.** -/
def memKeyT (dx : ℕ) (X : LTerm) (d : ℕ) (L : LTerm) : LTerm :=
  exE d L (natEqT dx (lift 2 X) (d + 1) (entryT d (lift 2 L) (.var 1)))

theorem eval_memKeyT (hM : y.length + 2 ≤ M) {dx d : ℕ} {X L : LTerm} {env : List ℕ} {x : ℕ}
    {F : Fmt} {l : List F.ty} {key : F.ty → ℕ} (hx : At y dx (eval y M env X) .nat x)
    (h : At y d (eval y M env L) (.list F) l) (hk : Key y (d + 1) F key) :
    eval y M env (memKeyT dx X d L) ≠ 0 ↔ x ∈ l.map key := by
  rw [memKeyT, eval_exE hM h, List.mem_iff_getElem]
  simp only [List.length_map, List.getElem_map]
  refine exists_congr fun i => ⟨fun ⟨hi, he⟩ => ⟨hi, ?_⟩, fun ⟨hi, he⟩ => ⟨hi, ?_⟩⟩
  · rw [eval_natEqT hM (hx.lift2 0 i) (hk _ _ (At.entry2 hM h hi 0))] at he
    by_contra hne; exact he (by rw [if_neg (Ne.symm hne)])
  · rw [eval_natEqT hM (hx.lift2 0 i) (hk _ _ (At.entry2 hM h hi 0)), if_pos he.symm]; simp

/-- **The keys of the list at `(d, L)` are distinct.** -/
def nodupKeyT (d : ℕ) (L : LTerm) : LTerm :=
  allE d L (allE d (lift 2 L) (or (not (.lt (.var 3) (.var 1)))
    (not (natEqT (d + 1) (entryT d (lift 2 (lift 2 L)) (.var 3)) (d + 1) (entryT d (lift 2 (lift 2 L)) (.var 1))))))

theorem eval_nodupKeyT (hM : y.length + 2 ≤ M) {d : ℕ} {L : LTerm} {env : List ℕ}
    {F : Fmt} {l : List F.ty} {key : F.ty → ℕ} (h : At y d (eval y M env L) (.list F) l)
    (hk : Key y (d + 1) F key) :
    eval y M env (nodupKeyT d L) ≠ 0 ↔ (l.map key).Nodup := by
  rw [nodupKeyT, eval_allE hM h, List.Nodup, List.pairwise_iff_getElem]
  simp only [List.length_map, List.getElem_map]
  refine ⟨fun H i j hi hj hij => ?_, fun H i hi => ?_⟩
  · have := (eval_allE hM (h.lift2 1 i) _).1 (H i hi) j hj
    have hi' : At y (d + 1) (eval y M (1 :: j :: 1 :: i :: env) (entryT d (lift 2 (lift 2 L)) (.var 3))) F l[i] :=
      At.entry hM (by rw [eval_lift2, eval_lift2]; exact h) hi (by simp [eval])
    have hj' := At.entry2 hM (h.lift2 1 i) hj 1
    rw [eval_or, eval_not, eval_not, eval_natEqT hM (hk _ _ hi') (hk _ _ hj')] at this
    simp only [eval, List.getD_cons_succ, List.getD_cons_zero] at this
    intro he
    simp [hij, he] at this
  · rw [eval_allE hM (h.lift2 1 i)]
    intro j hj
    have hi' : At y (d + 1) (eval y M (1 :: j :: 1 :: i :: env) (entryT d (lift 2 (lift 2 L)) (.var 3))) F l[i] :=
      At.entry hM (by rw [eval_lift2, eval_lift2]; exact h) hi (by simp [eval])
    have hj' := At.entry2 hM (h.lift2 1 i) hj 1
    rw [eval_or, eval_not, eval_not, eval_natEqT hM (hk _ _ hi') (hk _ _ hj')]
    simp only [eval, List.getD_cons_succ, List.getD_cons_zero]
    by_cases hij : i < j
    · simp [hij, H i j hi hj hij]
    · simp [hij]

/-- `#{j < n | B}`; the body sees `j` as variable `0`. -/
def cntT (n B : LTerm) : LTerm := .fold n (.lit 0) (.add (.var 0) (tst (lift 1 B)))

theorem eval_cntT {env : List ℕ} (n B : LTerm) (hn : eval y M env n ≤ M) :
    eval y M env (cntT n B) =
      ((List.range (eval y M env n)).filter fun j => eval y M (j :: env) B ≠ 0).length := by
  rw [cntT]
  simp only [eval]
  generalize eval y M env n = N at hn
  have key : ∀ k ≤ N, (List.range k).foldl (fun acc j => eval y M (acc :: j :: env)
      (.add (.var 0) (tst (lift 1 B)))) 0 = ((List.range k).filter fun j => eval y M (j :: env) B ≠ 0).length := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, ih (by omega), List.filter_append, List.length_append]
      have hle : ((List.range k).filter fun j => eval y M (j :: env) B ≠ 0).length ≤ k :=
        (List.length_filter_le _ _).trans (by simp)
      generalize ((List.range k).filter fun j => eval y M (j :: env) B ≠ 0).length = c at hle ⊢
      by_cases hb : eval y M (k :: env) B = 0
      · simp [eval, eval_lift1, hb]; omega
      · simp [eval, eval_lift1, hb]; omega
  exact key N le_rfl

end Logspace

end HTN
