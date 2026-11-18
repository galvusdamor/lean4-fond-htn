import Mathlib

/-!
# Anonymous runs of identical threads

A system of `k` threads with local states in `σ` and a shared state in `F`.  A step moves one
thread by the local step relation `ls`, which may also change the shared state.  Every thread
carries a *class* `κ j` that does not change.

The *anonymous* system forgets which thread is which.  Its configurations are a shared state and
the multiset of pairs (class, local state).  A step moves one element of the multiset.

* **`HTN.RegRounds.Anon.tRun_of_mRun`** — every anonymous run from the multiset of a thread
  configuration is the image of a thread run, with the same shared states.
* `HTN.RegRounds.Steps` — runs of a given length; `tSteps_of_mSteps` and `mSteps_of_tSteps` keep the
  length.
* **`HTN.RegRounds.Anon.tRun_of_mRun_end`** — if the anonymous run ends with every element of
  class `κ` in the state `e κ`, then every thread `j` ends in the state `e (κ j)`.

This is the per-round step of the native simulation of `HTN-REGM` thread pools (PROOFIDEAS
§15.4): within a round the compiled domain only keeps the counts per (class, state), and the
classes are fixed by the instance rows.
-/

namespace HTN

namespace RegRounds

/-- **Runs of length `n`.** -/
inductive Steps {α : Type*} (r : α → α → Prop) : ℕ → α → α → Prop
  | zero {a : α} : Steps r 0 a a
  | succ {n : ℕ} {a b c : α} : Steps r n a b → r b c → Steps r (n + 1) a c

namespace Steps

variable {α : Type*} {r : α → α → Prop}

theorem trans {m n : ℕ} {a b c : α} (h₁ : Steps r m a b) (h₂ : Steps r n b c) :
    Steps r (m + n) a c := by
  induction h₂ with
  | zero => simpa using h₁
  | succ _ hbc ih => exact Steps.succ (ih h₁) hbc

theorem single {a b : α} (h : r a b) : Steps r 1 a b := Steps.succ Steps.zero h

theorem rtg {n : ℕ} {a b : α} (h : Steps r n a b) : Relation.ReflTransGen r a b := by
  induction h with
  | zero => exact .refl
  | succ _ hbc ih => exact ih.tail hbc

theorem mono {r' : α → α → Prop} (hr : ∀ a b, r a b → r' a b) {n : ℕ} {a b : α}
    (h : Steps r n a b) : Steps r' n a b := by
  induction h with
  | zero => exact Steps.zero
  | succ _ hbc ih => exact Steps.succ ih (hr _ _ hbc)

end Steps

namespace Anon

variable {F σ κT : Type*} [DecidableEq σ] [DecidableEq κT]

/-- A thread configuration: the shared state and the local state of every thread. -/
structure TCfg (F σ : Type*) where
  sh : F
  th : ℕ → σ

/-- **A thread step**: one thread `j < k` moves by `ls`. -/
inductive TStep (ls : F → σ → F → σ → Prop) (k : ℕ) : TCfg F σ → TCfg F σ → Prop
  | mk {c : TCfg F σ} {j : ℕ} {f' : F} {s' : σ} (hj : j < k) (h : ls c.sh (c.th j) f' s') :
      TStep ls k c ⟨f', Function.update c.th j s'⟩

/-- An anonymous configuration: the shared state and a multiset of (class, local state). -/
structure MCfg (F σ κT : Type*) where
  sh : F
  ms : Multiset (κT × σ)

/-- **An anonymous step**: one element `(a, s)` of the multiset moves to `(a, s')` by `ls`. -/
inductive MStep (ls : F → σ → F → σ → Prop) : MCfg F σ κT → MCfg F σ κT → Prop
  | mk {c : MCfg F σ κT} {a : κT} {s f' s'} (hm : (a, s) ∈ c.ms) (h : ls c.sh s f' s') :
      MStep ls c ⟨f', (c.ms.erase (a, s)) + {(a, s')}⟩

/-- The multiset of (class, state) of the threads `j < k`. -/
def msOf (cls : ℕ → κT) (k : ℕ) (th : ℕ → σ) : Multiset (κT × σ) :=
  (Finset.range k).val.map fun i => (cls i, th i)

omit [DecidableEq σ] [DecidableEq κT] in
theorem exists_of_mem_msOf {cls : ℕ → κT} {k : ℕ} {th : ℕ → σ} {a : κT} {s : σ}
    (h : (a, s) ∈ msOf cls k th) : ∃ j < k, cls j = a ∧ th j = s := by
  simp only [msOf, Multiset.mem_map, Finset.mem_val, Finset.mem_range, Prod.mk.injEq] at h
  obtain ⟨j, hj, h1, h2⟩ := h
  exact ⟨j, hj, h1, h2⟩

/-- Updating one thread replaces one element of the multiset. -/
theorem msOf_update (cls : ℕ → κT) {k : ℕ} (th : ℕ → σ) {j : ℕ} (hj : j < k) (s' : σ) :
    msOf cls k (Function.update th j s') = (msOf cls k th).erase (cls j, th j) + {(cls j, s')} := by
  have hmem : j ∈ Finset.range k := Finset.mem_range.2 hj
  have hsplit : ∀ g : ℕ → κT × σ,
      (Finset.range k).val.map g = g j ::ₘ ((Finset.range k).erase j).val.map g := by
    intro g
    conv_lhs => rw [← Finset.insert_erase hmem]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase j _), Multiset.map_cons]
  have hrest : ((Finset.range k).erase j).val.map (fun i => (cls i, Function.update th j s' i)) =
      ((Finset.range k).erase j).val.map (fun i => (cls i, th i)) := by
    refine Multiset.map_congr rfl fun i hi => ?_
    have : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Function.update_of_ne this]
  simp only [msOf]
  rw [hsplit, hsplit (fun i => (cls i, th i)), hrest, Multiset.erase_cons_head]
  simp [add_comm]

/-- **Anonymous runs come from thread runs.** -/
theorem tRun_of_mRun (ls : F → σ → F → σ → Prop) (cls : ℕ → κT) (k : ℕ) {m m' : MCfg F σ κT}
    (h : Relation.ReflTransGen (MStep ls) m m') :
    ∀ c : TCfg F σ, c.sh = m.sh → msOf cls k c.th = m.ms →
      ∃ c' : TCfg F σ, Relation.ReflTransGen (TStep ls k) c c' ∧ c'.sh = m'.sh ∧
        msOf cls k c'.th = m'.ms := by
  induction h with
  | refl => exact fun c h1 h2 => ⟨c, .refl, h1, h2⟩
  | @tail b b' _ hstep ih =>
    intro c h1 h2
    obtain ⟨c₁, hr, hsh, hms⟩ := ih c h1 h2
    cases hstep with
    | @mk a s f' s' hm hls =>
      rw [← hms] at hm
      obtain ⟨j, hj, hcls, hth⟩ := exists_of_mem_msOf hm
      refine ⟨⟨f', Function.update c₁.th j s'⟩, hr.tail ?_, rfl, ?_⟩
      · have : ls c₁.sh (c₁.th j) f' s' := by rw [hsh, hth]; exact hls
        exact TStep.mk hj this
      · rw [msOf_update cls c₁.th hj s', hms, hcls, hth]

/-- **End states by class.**  If the anonymous run ends with every element of class `a` in
the state `e a`, then every thread ends in the end state of its class. -/
theorem tRun_of_mRun_end (ls : F → σ → F → σ → Prop) (cls : ℕ → κT) (k : ℕ) (e : κT → σ)
    {c : TCfg F σ} {m' : MCfg F σ κT}
    (h : Relation.ReflTransGen (MStep ls) ⟨c.sh, msOf cls k c.th⟩ m')
    (hend : ∀ x ∈ m'.ms, x.2 = e x.1) :
    ∃ c' : TCfg F σ, Relation.ReflTransGen (TStep ls k) c c' ∧ c'.sh = m'.sh ∧
      ∀ j < k, c'.th j = e (cls j) := by
  obtain ⟨c', hr, hsh, hms⟩ := tRun_of_mRun ls cls k h c rfl rfl
  refine ⟨c', hr, hsh, fun j hj => ?_⟩
  have hmem : (cls j, c'.th j) ∈ m'.ms := by
    rw [← hms]
    simp only [msOf, Multiset.mem_map, Finset.mem_val, Finset.mem_range]
    exact ⟨j, hj, rfl⟩
  exact hend _ hmem

/-- Conversely, thread runs give anonymous runs (so the two systems agree on the classes). -/
theorem mRun_of_tRun (ls : F → σ → F → σ → Prop) (cls : ℕ → κT) (k : ℕ) {c c' : TCfg F σ}
    (h : Relation.ReflTransGen (TStep ls k) c c') :
    Relation.ReflTransGen (MStep ls) (⟨c.sh, msOf cls k c.th⟩ : MCfg F σ κT)
      ⟨c'.sh, msOf cls k c'.th⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b b' _ hstep ih =>
    refine ih.tail ?_
    cases hstep with
    | @mk j f' s' hj hls =>
      have hm : (cls j, b.th j) ∈ msOf cls k b.th := by
        simp only [msOf, Multiset.mem_map, Finset.mem_val, Finset.mem_range]
        exact ⟨j, hj, rfl⟩
      have := MStep.mk (ls := ls) (c := (⟨b.sh, msOf cls k b.th⟩ : MCfg F σ κT)) hm hls
      simpa [msOf_update cls b.th hj s'] using this

/-- **Anonymous runs come from thread runs of the same length.** -/
theorem tSteps_of_mSteps (ls : F → σ → F → σ → Prop) (cls : ℕ → κT) (k : ℕ) {n : ℕ}
    {m m' : MCfg F σ κT} (h : Steps (MStep ls) n m m') :
    ∀ c : TCfg F σ, c.sh = m.sh → msOf cls k c.th = m.ms →
      ∃ c' : TCfg F σ, Steps (TStep ls k) n c c' ∧ c'.sh = m'.sh ∧ msOf cls k c'.th = m'.ms := by
  induction h with
  | zero => exact fun c h1 h2 => ⟨c, Steps.zero, h1, h2⟩
  | @succ n b b' b'' _ hstep ih =>
    intro c h1 h2
    obtain ⟨c₁, hr, hsh, hms⟩ := ih c h1 h2
    cases hstep with
    | @mk a s f' s' hm hls =>
      rw [← hms] at hm
      obtain ⟨j, hj, hcls, hth⟩ := exists_of_mem_msOf hm
      refine ⟨⟨f', Function.update c₁.th j s'⟩, Steps.succ hr ?_, rfl, ?_⟩
      · have : ls c₁.sh (c₁.th j) f' s' := by rw [hsh, hth]; exact hls
        exact TStep.mk hj this
      · rw [msOf_update cls c₁.th hj s', hms, hcls, hth]

/-- Thread runs give anonymous runs of the same length. -/
theorem mSteps_of_tSteps (ls : F → σ → F → σ → Prop) (cls : ℕ → κT) (k : ℕ) {n : ℕ}
    {c c' : TCfg F σ} (h : Steps (TStep ls k) n c c') :
    Steps (MStep ls) n (⟨c.sh, msOf cls k c.th⟩ : MCfg F σ κT) ⟨c'.sh, msOf cls k c'.th⟩ := by
  induction h with
  | zero => exact Steps.zero
  | @succ n b b' b'' _ hstep ih =>
    refine Steps.succ ih ?_
    cases hstep with
    | @mk j f' s' hj hls =>
      have hm : (cls j, b'.th j) ∈ msOf cls k b'.th := by
        simp only [msOf, Multiset.mem_map, Finset.mem_val, Finset.mem_range]
        exact ⟨j, hj, rfl⟩
      have := MStep.mk (ls := ls) (c := (⟨b'.sh, msOf cls k b'.th⟩ : MCfg F σ κT)) hm hls
      simpa [msOf_update cls b'.th hj s'] using this

end Anon

end RegRounds

end HTN
