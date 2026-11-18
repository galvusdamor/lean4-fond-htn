import HtnComplexity.Computable.StackMachine
import HtnComplexity.Computable.RegStrips
/-!
# The compiled `STRIPS` description of a totally ordered tail-recursive description

This file builds the `STRIPS` description that simulates the bounded stack machine of
`HtnComplexity/Computable/StackMachine.lean`, and computes the precondition, add and
delete list of each of its actions.  The correctness of the simulation is
`HtnComplexity/Computable/TrStripsCorrect.lean`.

## The facts

A fact of the compiled description is a number; the six kinds are told apart by the residue
modulo `6`:

| fact | number | meaning |
| --- | --- | --- |
| `encSt v` | `6v` | the fact `v` of the source problem holds |
| `encCur i m j` | `6⟨i, m, j⟩ + 1` | the **active** frame is at depth `i`: method `m`, next subtask `j` |
| `encSav i m j` | `6⟨i, m, j⟩ + 2` | a **suspended** frame at depth `i` |
| `encCall c` | `6c + 3` | the initial compound task `c` has not been started |
| `encDone` | `4` | the initial task network has been refined completely |
| `encBot` | `5` | unsatisfiable: the guard of an action that must never be applied |

A stack `[(m₀, j₀), …, (m_k, j_k)]` — innermost frame first — is encoded as the active fact of
its head together with the suspended facts of its tail, the depth of a frame being the number
of frames below it (`HTN.Syn.ctlSet`).

## The actions

Six kinds, all of them with a *constant* effect, so that they can be listed:

| kind | precondition | add | delete |
| --- | --- | --- | --- |
| `beg m` | `call (hd m)` | `cur 0 m 0` | `call (hd m)` |
| `exec i m j` | `cur i m j`, `prec a` | `cur i m (j+1)`, `add a` | `cur i m j`, `del a` |
| `push i m j m'` | `cur i m j` | `cur (i+1) m' 0`, `sav i m (j+1)` | `cur i m j` |
| `tail i m j m'` | `cur i m j` | `cur i m' 0` | `cur i m j` |
| `ret i m j' m'` | `cur i m |bd m|`, `sav (i-1) m' j'` | `cur (i-1) m' j'` | both |
| `fin m` | `cur 0 m |bd m|` | `done` | `cur 0 m |bd m|` |

where `a` is the action at position `j` of the body of `m` and, for the compound kinds, the
compound task there is the one the method `m'` decomposes.  A parameter tuple that does not
describe a legal step of the machine — a `push` beyond the depth bound, an `exec` at a position
that is not primitive, and so on — gets the unsatisfiable precondition `encBot`.

The actions are enumerated by the box of parameter tuples `HTN.Syn.cacts`, and their names are
their positions in that enumeration.
-/

namespace HTN

namespace Syn

/-! ### The facts -/

/-- A fact of the source problem. -/
def encSt (v : ℕ) : ℕ := 6 * v

/-- The active frame at depth `i`. -/
def encCur (i m j : ℕ) : ℕ := 6 * Nat.pair i (Nat.pair m j) + 1

/-- A suspended frame at depth `i`. -/
def encSav (i m j : ℕ) : ℕ := 6 * Nat.pair i (Nat.pair m j) + 2

/-- The initial compound task, not yet started. -/
def encCall (c : ℕ) : ℕ := 6 * c + 3

/-- The initial task network has been refined completely. -/
def encDone : ℕ := 4

/-- The unsatisfiable fact. -/
def encBot : ℕ := 5

@[simp] theorem encSt_mod (v : ℕ) : encSt v % 6 = 0 := by simp [encSt, Nat.mul_mod_right]

@[simp] theorem encCur_mod (i m j : ℕ) : encCur i m j % 6 = 1 := by
  simp only [encCur]; omega

@[simp] theorem encSav_mod (i m j : ℕ) : encSav i m j % 6 = 2 := by
  simp only [encSav]; omega

@[simp] theorem encCall_mod (c : ℕ) : encCall c % 6 = 3 := by
  simp only [encCall]; omega

@[simp] theorem encDone_mod : encDone % 6 = 4 := by simp [encDone]

@[simp] theorem encBot_mod : encBot % 6 = 5 := by simp [encBot]

theorem encSt_injective : Function.Injective encSt := by
  intro a b h
  simpa [encSt] using h

@[simp] theorem encCur_inj {i m j i' m' j' : ℕ} :
    encCur i m j = encCur i' m' j' ↔ i = i' ∧ m = m' ∧ j = j' := by
  constructor
  · intro h
    have h1 : Nat.pair i (Nat.pair m j) = Nat.pair i' (Nat.pair m' j') := by
      simp only [encCur] at h; omega
    have h2 := (Nat.pair_eq_pair.1 h1)
    have h3 := Nat.pair_eq_pair.1 h2.2
    exact ⟨h2.1, h3.1, h3.2⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

@[simp] theorem encSav_inj {i m j i' m' j' : ℕ} :
    encSav i m j = encSav i' m' j' ↔ i = i' ∧ m = m' ∧ j = j' := by
  constructor
  · intro h
    have h1 : Nat.pair i (Nat.pair m j) = Nat.pair i' (Nat.pair m' j') := by
      simp only [encSav] at h; omega
    have h2 := (Nat.pair_eq_pair.1 h1)
    have h3 := Nat.pair_eq_pair.1 h2.2
    exact ⟨h2.1, h3.1, h3.2⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

@[simp] theorem encCall_inj {c c' : ℕ} : encCall c = encCall c' ↔ c = c' := by
  simp only [encCall]; omega

/-! ### States of the compiled problem -/

/-- The encoded facts of a source state. -/
def stSet (s : Set ℕ) : Set ℕ := encSt '' s

@[simp] theorem mem_stSet_encSt {s : Set ℕ} {v : ℕ} : encSt v ∈ stSet s ↔ v ∈ s := by
  simp only [stSet, Set.mem_image]
  exact ⟨fun ⟨w, hw, h⟩ => (encSt_injective h) ▸ hw, fun h => ⟨v, h, rfl⟩⟩

theorem mem_stSet_iff {s : Set ℕ} {x : ℕ} : x ∈ stSet s ↔ ∃ v ∈ s, encSt v = x := Iff.rfl

theorem mod_zero_of_mem_stSet {s : Set ℕ} {x : ℕ} (h : x ∈ stSet s) : x % 6 = 0 := by
  obtain ⟨v, -, rfl⟩ := h
  simp

theorem notMem_stSet_of_mod {s : Set ℕ} {x : ℕ} (h : x % 6 ≠ 0) : x ∉ stSet s :=
  fun hx => h (mod_zero_of_mem_stSet hx)

@[simp] theorem stSet_empty : stSet (∅ : Set ℕ) = ∅ := Set.image_empty _

/-- The suspended frames of a stack. -/
def savSet : List (ℕ × ℕ) → Set ℕ
  | [] => ∅
  | (m, j) :: rest => insert (encSav rest.length m j) (savSet rest)

/-- The control facts of a stack: the active frame on top, the suspended frames below. -/
def ctlSet : List (ℕ × ℕ) → Set ℕ
  | [] => ∅
  | (m, j) :: rest => insert (encCur rest.length m j) (savSet rest)

@[simp] theorem savSet_nil : savSet [] = ∅ := rfl

@[simp] theorem savSet_cons (m j : ℕ) (rest : List (ℕ × ℕ)) :
    savSet ((m, j) :: rest) = insert (encSav rest.length m j) (savSet rest) := rfl

@[simp] theorem ctlSet_nil : ctlSet [] = ∅ := rfl

@[simp] theorem ctlSet_cons (m j : ℕ) (rest : List (ℕ × ℕ)) :
    ctlSet ((m, j) :: rest) = insert (encCur rest.length m j) (savSet rest) := rfl

theorem mod_two_of_mem_savSet {st : List (ℕ × ℕ)} {x : ℕ} (h : x ∈ savSet st) : x % 6 = 2 := by
  induction st with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨m, j⟩ := p
    rcases Set.mem_insert_iff.1 h with rfl | h
    · simp
    · exact ih h

theorem mod_of_mem_ctlSet {st : List (ℕ × ℕ)} {x : ℕ} (h : x ∈ ctlSet st) :
    x % 6 = 1 ∨ x % 6 = 2 := by
  rcases st with _ | ⟨⟨m, j⟩, rest⟩
  · simp at h
  · rcases Set.mem_insert_iff.1 h with rfl | h
    · exact Or.inl (encCur_mod _ _ _)
    · exact Or.inr (mod_two_of_mem_savSet h)

theorem mod_ne_zero_of_mem_ctlSet {st : List (ℕ × ℕ)} {x : ℕ} (h : x ∈ ctlSet st) : x % 6 ≠ 0 := by
  rcases mod_of_mem_ctlSet h with h' | h' <;> omega

/-- The active fact determines the top frame of the stack. -/
theorem encCur_mem_ctlSet_iff {i m j : ℕ} {st : List (ℕ × ℕ)} :
    encCur i m j ∈ ctlSet st ↔ ∃ rest, st = (m, j) :: rest ∧ rest.length = i := by
  rcases st with _ | ⟨⟨m₀, j₀⟩, rest⟩
  · simp
  · simp only [ctlSet_cons, Set.mem_insert_iff]
    constructor
    · rintro (h | h)
      · obtain ⟨hi, hm, hj⟩ := encCur_inj.1 h.symm
        subst hm; subst hj
        exact ⟨rest, rfl, hi⟩
      · exact absurd (mod_two_of_mem_savSet h) (by simp)
    · rintro ⟨rest', h, hlen⟩
      obtain ⟨h1, h2⟩ := List.cons_eq_cons.1 h
      rw [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      subst h2
      exact Or.inl (by rw [hlen])

theorem lt_length_of_encSav_mem {n m j : ℕ} {st : List (ℕ × ℕ)} (h : encSav n m j ∈ savSet st) :
    n < st.length := by
  induction st with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨m₀, j₀⟩ := p
    rcases Set.mem_insert_iff.1 h with h | h
    · obtain ⟨hn, -, -⟩ := encSav_inj.1 h
      simp [hn]
    · have := ih h
      simp only [List.length_cons]
      omega

/-- The topmost suspended fact determines the frame below the active one. -/
theorem encSav_mem_savSet_top {n m j : ℕ} {st : List (ℕ × ℕ)} (h : encSav n m j ∈ savSet st)
    (hlen : n + 1 = st.length) : ∃ tl, st = (m, j) :: tl ∧ tl.length = n := by
  rcases st with _ | ⟨⟨m₀, j₀⟩, rest⟩
  · simp at h
  · rcases Set.mem_insert_iff.1 h with h | h
    · obtain ⟨hn, hm, hj⟩ := encSav_inj.1 h
      subst hm; subst hj
      exact ⟨rest, rfl, hn.symm⟩
    · exfalso
      have := lt_length_of_encSav_mem h
      simp only [List.length_cons] at hlen
      omega

/-- **The compiled state** of a source state and a stack. -/
def cfg (s : Set ℕ) (st : List (ℕ × ℕ)) : Set ℕ := stSet s ∪ ctlSet st

/-- **The compiled state** after the initial task network has been refined completely. -/
def endCfg (s : Set ℕ) : Set ℕ := insert encDone (stSet s)

/-- **The compiled initial state**, before the initial compound task has been started. -/
def startCfg (s : Set ℕ) (c : ℕ) : Set ℕ := insert (encCall c) (stSet s)

/-! ### Set algebra -/

/-- The effects of a compiled action split into a source part and a control part. -/
theorem transition_split (s D A : Set ℕ) (Csrc Cdel Cadd : Set ℕ)
    (hCsrc : ∀ x ∈ Csrc, x % 6 ≠ 0) (hCdel : ∀ x ∈ Cdel, x % 6 ≠ 0)
    (hCadd : ∀ x ∈ Cadd, x % 6 ≠ 0) :
    (((stSet s ∪ Csrc) \ (stSet D ∪ Cdel)) ∪ (stSet A ∪ Cadd))
      = stSet ((s \ D) ∪ A) ∪ ((Csrc \ Cdel) ∪ Cadd) := by
  ext x
  by_cases hx : x % 6 = 0
  · have hxv : encSt (x / 6) = x := by
      simp only [encSt]
      omega
    have hC : x ∉ Csrc := fun h => hCsrc x h hx
    have hCd : x ∉ Cdel := fun h => hCdel x h hx
    have hCa : x ∉ Cadd := fun h => hCadd x h hx
    constructor
    · rintro (⟨hmem, hnot⟩ | hmem)
      · rcases hmem with hmem | hmem
        · obtain ⟨v, hv, rfl⟩ := hmem
          exact Or.inl ⟨v, Or.inl ⟨hv, fun hD => hnot (Or.inl ⟨v, hD, rfl⟩)⟩, rfl⟩
        · exact absurd hmem hC
      · rcases hmem with hmem | hmem
        · obtain ⟨v, hv, rfl⟩ := hmem
          exact Or.inl ⟨v, Or.inr hv, rfl⟩
        · exact absurd hmem hCa
    · rintro (hmem | hmem)
      · obtain ⟨v, hv, rfl⟩ := hmem
        rcases hv with ⟨hv, hnD⟩ | hv
        · refine Or.inl ⟨Or.inl ⟨v, hv, rfl⟩, ?_⟩
          rintro (h | h)
          · obtain ⟨w, hw, hwv⟩ := h
            exact hnD ((encSt_injective hwv) ▸ hw)
          · exact hCd h
        · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
      · rcases hmem with ⟨hmem, -⟩ | hmem
        · exact absurd hmem hC
        · exact absurd hmem hCa
  · have hs : x ∉ stSet s := notMem_stSet_of_mod hx
    have hD : x ∉ stSet D := notMem_stSet_of_mod hx
    have hA : x ∉ stSet A := notMem_stSet_of_mod hx
    have hSA : x ∉ stSet ((s \ D) ∪ A) := notMem_stSet_of_mod hx
    constructor
    · rintro (⟨hmem, hnot⟩ | hmem)
      · rcases hmem with hmem | hmem
        · exact absurd hmem hs
        · exact Or.inr (Or.inl ⟨hmem, fun h => hnot (Or.inr h)⟩)
      · rcases hmem with hmem | hmem
        · exact absurd hmem hA
        · exact Or.inr (Or.inr hmem)
    · rintro (hmem | hmem)
      · exact absurd hmem hSA
      · rcases hmem with ⟨hmem, hnot⟩ | hmem
        · exact Or.inl ⟨Or.inr hmem, fun h => by
            rcases h with h | h
            · exact hD h
            · exact hnot h⟩
        · exact Or.inr (Or.inr hmem)

/-- A precondition splits into a source part and a control part. -/
theorem subset_cfg_iff {P : Set ℕ} {Cp : Set ℕ} {s : Set ℕ} {C : Set ℕ}
    (hCp : ∀ x ∈ Cp, x % 6 ≠ 0) (hC : ∀ x ∈ C, x % 6 ≠ 0) :
    stSet P ∪ Cp ⊆ stSet s ∪ C ↔ P ⊆ s ∧ Cp ⊆ C := by
  constructor
  · intro h
    constructor
    · intro v hv
      rcases h (Or.inl ⟨v, hv, rfl⟩) with hmem | hmem
      · obtain ⟨w, hw, hwv⟩ := hmem
        exact (encSt_injective hwv) ▸ hw
      · exact absurd (encSt_mod v) (hC _ hmem)
    · exact fun x hx => (h (Or.inr hx)).resolve_left (notMem_stSet_of_mod (hCp x hx))
  · rintro ⟨hP, hC⟩ x hx
    rcases hx with hx | hx
    · obtain ⟨v, hv, rfl⟩ := hx
      exact Or.inl ⟨v, hP hv, rfl⟩
    · exact Or.inr (hC hx)

/-! ### The control part of the transitions -/

theorem ctl_step_cur (i m j m₂ j₂ : ℕ) {rest : List (ℕ × ℕ)} (h : rest.length = i) :
    ((ctlSet ((m, j) :: rest)) \ {encCur i m j}) ∪ {encCur i m₂ j₂} = ctlSet ((m₂, j₂) :: rest) := by
  subst h
  ext x
  simp only [ctlSet_cons, Set.mem_union, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨hmem | hmem, hne⟩ | rfl)
    · exact absurd hmem hne
    · exact Or.inr hmem
    · exact Or.inl rfl
  · rintro (rfl | hmem)
    · exact Or.inr rfl
    · exact Or.inl ⟨Or.inr hmem, fun hcon => by
        rw [hcon] at hmem
        exact absurd (mod_two_of_mem_savSet hmem) (by simp)⟩

theorem ctl_step_push (i m j m' : ℕ) {rest : List (ℕ × ℕ)} (h : rest.length = i) :
    ((ctlSet ((m, j) :: rest)) \ {encCur i m j}) ∪ {encCur (i + 1) m' 0, encSav i m (j + 1)}
      = ctlSet ((m', 0) :: (m, j + 1) :: rest) := by
  subst h
  ext x
  simp only [ctlSet_cons, savSet_cons, List.length_cons, Set.mem_union, Set.mem_diff,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨hmem | hmem, hne⟩ | rfl | rfl)
    · exact absurd hmem hne
    · exact Or.inr (Or.inr hmem)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rintro (rfl | rfl | hmem)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · refine Or.inl ⟨Or.inr hmem, fun hcon => ?_⟩
      rw [hcon] at hmem
      exact absurd (mod_two_of_mem_savSet hmem) (by simp)

theorem ctl_step_ret (m j m' j' : ℕ) {tl : List (ℕ × ℕ)} :
    ((ctlSet ((m, j) :: (m', j') :: tl)) \ {encCur (tl.length + 1) m j, encSav tl.length m' j'})
        ∪ {encCur tl.length m' j'} = ctlSet ((m', j') :: tl) := by
  ext x
  simp only [ctlSet_cons, savSet_cons, List.length_cons, Set.mem_union, Set.mem_diff,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨hmem | hmem | hmem, hne⟩ | rfl)
    · exact absurd (Or.inl hmem) hne
    · exact absurd (Or.inr hmem) hne
    · exact Or.inr hmem
    · exact Or.inl rfl
  · rintro (rfl | hmem)
    · exact Or.inr rfl
    · refine Or.inl ⟨Or.inr (Or.inr hmem), ?_⟩
      rintro (hcon | hcon)
      · rw [hcon] at hmem
        exact absurd (mod_two_of_mem_savSet hmem) (by simp)
      · rw [hcon] at hmem
        exact absurd (lt_length_of_encSav_mem hmem) (by omega)

theorem ctl_step_fin (m j : ℕ) :
    ((ctlSet [(m, j)]) \ {encCur 0 m j}) ∪ {encDone} = ({encDone} : Set ℕ) := by
  ext x
  simp only [ctlSet_cons, savSet_nil, List.length_nil, Set.mem_union, Set.mem_diff,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
  constructor
  · rintro (⟨rfl, hne⟩ | rfl)
    · exact absurd rfl hne
    · rfl
  · rintro rfl
    exact Or.inr rfl

theorem ctl_step_beg (c m : ℕ) :
    (({encCall c} : Set ℕ) \ {encCall c}) ∪ {encCur 0 m 0} = ctlSet [(m, 0)] := by
  ext x
  simp only [ctlSet_cons, savSet_nil, List.length_nil, Set.mem_union, Set.mem_diff,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
  constructor
  · rintro (⟨rfl, hne⟩ | rfl)
    · exact absurd rfl hne
    · rfl
  · rintro rfl
    exact Or.inr rfl

/-! ### The subtask at a position of a described method body -/

namespace DomDesc

/-- The label at position `j` of the body of the method at position `m`. -/
def bdAt (d : DomDesc) (m j : ℕ) : ℕ ⊕ ℕ := ((d.bd m)[j]?).getD (Sum.inl 0)

/-- Whether the task at position `j` of the body of the method `m` is compound. -/
def isCompAt (d : DomDesc) (m j : ℕ) : Bool := Sum.elim (fun _ => false) (fun _ => true) (bdAt d m j)

/-- The action at position `j` of the body of the method `m` (meaningless if it is compound). -/
def actAt (d : DomDesc) (m j : ℕ) : ℕ := Sum.elim id (fun _ => 0) (bdAt d m j)

/-- The compound task at position `j` of the body of `m` (meaningless if it is primitive). -/
def compAt (d : DomDesc) (m j : ℕ) : ℕ := Sum.elim (fun _ => 0) id (bdAt d m j)

theorem bdAt_eq_getElem {d : DomDesc} {m j : ℕ} (h : j < (d.bd m).length) :
    bdAt d m j = (d.bd m)[j] := by
  rw [bdAt, List.getElem?_eq_getElem h, Option.getD_some]

theorem isCompAt_false_iff {d : DomDesc} {m j a : ℕ} (h : j < (d.bd m).length) :
    (isCompAt d m j = false ∧ actAt d m j = a) ↔ (d.bd m)[j]? = some (Sum.inl a) := by
  rw [List.getElem?_eq_getElem h]
  have hb : bdAt d m j = (d.bd m)[j] := bdAt_eq_getElem h
  rcases hx : (d.bd m)[j] with b | c
  · rw [hx] at hb
    simp [isCompAt, actAt, hb]
  · rw [hx] at hb
    simp [isCompAt, actAt, hb]

theorem isCompAt_true_iff {d : DomDesc} {m j c : ℕ} (h : j < (d.bd m).length) :
    (isCompAt d m j = true ∧ compAt d m j = c) ↔ (d.bd m)[j]? = some (Sum.inr c) := by
  rw [List.getElem?_eq_getElem h]
  have hb : bdAt d m j = (d.bd m)[j] := bdAt_eq_getElem h
  rcases hx : (d.bd m)[j] with b | c'
  · rw [hx] at hb
    simp [isCompAt, compAt, hb]
  · rw [hx] at hb
    simp [isCompAt, compAt, hb]

end DomDesc

/-! ### The compiled actions -/

/-- The specification of an action that must never be applied. -/
def badSpec : List ℕ × List ℕ × List ℕ := ([encBot], [], [])

/-- **Start the initial compound task** with the method `m`. -/
def begSpec (d : DomDesc) (m : ℕ) : List ℕ × List ℕ × List ℕ :=
  if m < d.methods.length then
    ([encCall (d.hd m)], [encCur 0 m 0], [encCall (d.hd m)])
  else badSpec

/-- **Execute the primitive subtask** at position `j` of the method `m`, at depth `i`. -/
def execSpec (d : DomDesc) (i m j : ℕ) : List ℕ × List ℕ × List ℕ :=
  if j < (d.bd m).length ∧ d.isCompAt m j = false then
    (encCur i m j :: (d.precList (d.actAt m j)).map encSt,
     encCur i m (j + 1) :: (d.addList (d.actAt m j)).map encSt,
     encCur i m j :: (d.delList (d.actAt m j)).map encSt)
  else badSpec

/-- **Push a frame** for the compound subtask at position `j` of `m`, refined by `m'`. -/
def pushSpec (d : DomDesc) (i m j m' : ℕ) : List ℕ × List ℕ × List ℕ :=
  if j + 1 < (d.bd m).length ∧ d.isCompAt m j = true ∧ d.compAt m j = d.hd m' ∧
      m' < d.methods.length ∧ i + 1 < d.methods.length then
    ([encCur i m j], [encCur (i + 1) m' 0, encSav i m (j + 1)], [encCur i m j])
  else badSpec

/-- **Tail call**: the compound subtask at the last position of `m`, refined by `m'`. -/
def tailSpec (d : DomDesc) (i m j m' : ℕ) : List ℕ × List ℕ × List ℕ :=
  if j + 1 = (d.bd m).length ∧ d.isCompAt m j = true ∧ d.compAt m j = d.hd m' ∧
      m' < d.methods.length then
    ([encCur i m j], [encCur i m' 0], [encCur i m j])
  else badSpec

/-- **Return** from the finished frame `m` at depth `i` to the suspended frame `(m', j')`. -/
def retSpec (d : DomDesc) (i m j' m' : ℕ) : List ℕ × List ℕ × List ℕ :=
  if 0 < i then
    ([encCur i m (d.bd m).length, encSav (i - 1) m' j'], [encCur (i - 1) m' j'],
     [encCur i m (d.bd m).length, encSav (i - 1) m' j'])
  else badSpec

/-- **Finish**: the frame at depth `0` is exhausted. -/
def finSpec (d : DomDesc) (m : ℕ) : List ℕ × List ℕ × List ℕ :=
  ([encCur 0 m (d.bd m).length], [encDone], [encCur 0 m (d.bd m).length])

/-- The specification of the compiled action with the parameter tuple
`(kind, depth, method, position, method)`. -/
def specOf (d : DomDesc) (x : ℕ × ℕ × ℕ × ℕ × ℕ) : List ℕ × List ℕ × List ℕ :=
  if x.1 = 0 then begSpec d x.2.2.1
  else if x.1 = 1 then execSpec d x.2.1 x.2.2.1 x.2.2.2.1
  else if x.1 = 2 then pushSpec d x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  else if x.1 = 3 then tailSpec d x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  else if x.1 = 4 then retSpec d x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  else if x.1 = 5 then finSpec d x.2.2.1
  else badSpec

/-- The parameter tuples of the compiled actions. -/
def cacts (d : DomDesc) : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (List.range 6).flatMap fun k =>
    (List.range d.methods.length).flatMap fun i =>
      (List.range d.methods.length).flatMap fun m =>
        (List.range (d.size + 2)).flatMap fun j =>
          (List.range d.methods.length).map fun m' => (k, i, m, j, m')

theorem mem_cacts_iff {d : DomDesc} {x : ℕ × ℕ × ℕ × ℕ × ℕ} :
    x ∈ cacts d ↔ x.1 < 6 ∧ x.2.1 < d.methods.length ∧ x.2.2.1 < d.methods.length ∧
      x.2.2.2.1 < d.size + 2 ∧ x.2.2.2.2 < d.methods.length := by
  obtain ⟨k, i, m, j, m'⟩ := x
  simp only [cacts, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk, i', hi, m₀, hm, j₀, hj, m₁, hm', h1, h2, h3, h4, h5⟩
    subst h1; subst h2; subst h3; subst h4; subst h5
    exact ⟨hk, hi, hm, hj, hm'⟩
  · rintro ⟨hk, hi, hm, hj, hm'⟩
    exact ⟨k, hk, i, hi, m, hm, j, hj, m', hm', rfl, rfl, rfl, rfl, rfl⟩

theorem mem_cacts {d : DomDesc} {k i m j m' : ℕ} (hk : k < 6) (hi : i < d.methods.length)
    (hm : m < d.methods.length) (hj : j < d.size + 2) (hm' : m' < d.methods.length) :
    (k, i, m, j, m') ∈ cacts d :=
  mem_cacts_iff.2 ⟨hk, hi, hm, hj, hm'⟩

/-- The compiled actions: one per parameter tuple, named by its position. -/
def trActions (d : DomDesc) : List ActionDesc :=
  (List.range (cacts d).length).map fun n => (n, specOf d ((cacts d).getI n))

/-- **The compiled domain description.** -/
def trStripsDom (d : DomDesc) : DomDesc := stripsDom (trActions d)

/-- **The compiled instance description.** -/
def trStripsInst (q : InstDesc) : InstDesc :=
  stripsInst (q.initList.map encSt ++ [encCall (rootName q)])
    (q.goalList.map encSt ++ [encDone])

/-- The name of the compiled action with the parameter tuple `x`. -/
def nameOf (d : DomDesc) (x : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := (cacts d).idxOf x

theorem nameOf_lt {d : DomDesc} {x : ℕ × ℕ × ℕ × ℕ × ℕ} (h : x ∈ cacts d) :
    nameOf d x < (cacts d).length := List.idxOf_lt_length_of_mem h

theorem getI_nameOf {d : DomDesc} {x : ℕ × ℕ × ℕ × ℕ × ℕ} (h : x ∈ cacts d) :
    (cacts d).getI (nameOf d x) = x := by
  rw [List.getI_eq_getElem (l := cacts d) (nameOf_lt h)]
  exact List.getElem_idxOf (nameOf_lt h)

theorem lookup_trActions {d : DomDesc} {n : ℕ} (hn : n < (cacts d).length) :
    (trActions d).lookup n = some (specOf d ((cacts d).getI n)) :=
  lookup_map_of_fst (fun n => (n, specOf d ((cacts d).getI n))) (fun _ => rfl) _
    (List.mem_range.2 hn)

theorem actNames_trStripsDom (d : DomDesc) :
    (trStripsDom d).actNames = List.range (cacts d).length := by
  simp only [DomDesc.actNames, trStripsDom, stripsDom_actions, trActions, List.map_map]
  exact List.map_id'' (fun _ => rfl) _

theorem prec_trStripsDom {d : DomDesc} {n : ℕ} (hn : n < (cacts d).length) :
    (trStripsDom d).prec n = {f | f ∈ (specOf d ((cacts d).getI n)).1} := by
  simp [DomDesc.prec, trStripsDom, lookup_trActions hn]

theorem add_trStripsDom {d : DomDesc} {n : ℕ} (hn : n < (cacts d).length) :
    (trStripsDom d).add n = {f | f ∈ (specOf d ((cacts d).getI n)).2.1} := by
  simp [DomDesc.add, trStripsDom, lookup_trActions hn]

theorem del_trStripsDom {d : DomDesc} {n : ℕ} (hn : n < (cacts d).length) :
    (trStripsDom d).del n = {f | f ∈ (specOf d ((cacts d).getI n)).2.2} := by
  simp [DomDesc.del, trStripsDom, lookup_trActions hn]

theorem prec_nameOf {d : DomDesc} {x : ℕ × ℕ × ℕ × ℕ × ℕ} (h : x ∈ cacts d) :
    (trStripsDom d).prec (nameOf d x) = {f | f ∈ (specOf d x).1} := by
  rw [prec_trStripsDom (nameOf_lt h), getI_nameOf h]

theorem add_nameOf {d : DomDesc} {x : ℕ × ℕ × ℕ × ℕ × ℕ} (h : x ∈ cacts d) :
    (trStripsDom d).add (nameOf d x) = {f | f ∈ (specOf d x).2.1} := by
  rw [add_trStripsDom (nameOf_lt h), getI_nameOf h]

theorem del_nameOf {d : DomDesc} {x : ℕ × ℕ × ℕ × ℕ × ℕ} (h : x ∈ cacts d) :
    (trStripsDom d).del (nameOf d x) = {f | f ∈ (specOf d x).2.2} := by
  rw [del_trStripsDom (nameOf_lt h), getI_nameOf h]

/-! ### Lists of facts, as sets -/

theorem setOf_mem_cons (x : ℕ) (l : List ℕ) : {f | f ∈ x :: l} = insert x {f | f ∈ l} := by
  ext y; simp

theorem setOf_mem_map_encSt (l : List ℕ) : {f | f ∈ l.map encSt} = stSet {v | v ∈ l} := by
  ext y
  simp only [Set.mem_setOf_eq, List.mem_map, stSet, Set.mem_image]

theorem setOf_mem_cons_map (x : ℕ) (l : List ℕ) :
    {f | f ∈ x :: l.map encSt} = stSet {v | v ∈ l} ∪ {x} := by
  rw [setOf_mem_cons, setOf_mem_map_encSt]
  ext y
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
  tauto

theorem setOf_mem_pair (x y : ℕ) : {f | f ∈ [x, y]} = ({x, y} : Set ℕ) := by
  ext z; simp

theorem setOf_mem_singleton (x : ℕ) : {f | f ∈ [x]} = ({x} : Set ℕ) := by
  ext z; simp

theorem setOf_mem_nil : {f | f ∈ ([] : List ℕ)} = (∅ : Set ℕ) := by
  ext z; simp

/-! ### Unfolding the specification of an action -/

variable {d : DomDesc}

@[simp] theorem specOf_beg (i m j m' : ℕ) : specOf d (0, i, m, j, m') = begSpec d m := by
  simp [specOf]

@[simp] theorem specOf_exec (i m j m' : ℕ) : specOf d (1, i, m, j, m') = execSpec d i m j := by
  simp [specOf]

@[simp] theorem specOf_push (i m j m' : ℕ) : specOf d (2, i, m, j, m') = pushSpec d i m j m' := by
  simp [specOf]

@[simp] theorem specOf_tail (i m j m' : ℕ) : specOf d (3, i, m, j, m') = tailSpec d i m j m' := by
  simp [specOf]

@[simp] theorem specOf_ret (i m j m' : ℕ) : specOf d (4, i, m, j, m') = retSpec d i m j m' := by
  simp [specOf]

@[simp] theorem specOf_fin (i m j m' : ℕ) : specOf d (5, i, m, j, m') = finSpec d m := by
  simp [specOf]

theorem specOf_other {k i m j m' : ℕ} (hk : 6 ≤ k) : specOf d (k, i, m, j, m') = badSpec := by
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  have h2 : k ≠ 2 := by omega
  have h3 : k ≠ 3 := by omega
  have h4 : k ≠ 4 := by omega
  have h5 : k ≠ 5 := by omega
  simp [specOf, h0, h1, h2, h3, h4, h5]

/-! ### The precondition, add and delete set of a compiled action -/

/-- The unsatisfiable precondition of an action that must never be applied. -/
theorem prec_of_badSpec {n : ℕ} (hn : n < (cacts d).length)
    (h : specOf d ((cacts d).getI n) = badSpec) : (trStripsDom d).prec n = {encBot} := by
  rw [prec_trStripsDom hn, h]
  exact setOf_mem_singleton _

theorem encBot_mem_of_applicable_bad {n : ℕ} {X : Set ℕ} (hn : n < (cacts d).length)
    (h : specOf d ((cacts d).getI n) = badSpec)
    (happ : (trStripsDom d).toDomain.Applicable n X) : encBot ∈ X := by
  refine happ ?_
  show encBot ∈ (trStripsDom d).prec n
  rw [prec_of_badSpec hn h]
  rfl

section Beg

variable {n i m j m' : ℕ}

theorem prec_beg (hn : n < (cacts d).length) (hget : (cacts d).getI n = (0, i, m, j, m'))
    (hm : m < d.methods.length) :
    (trStripsDom d).prec n = stSet ∅ ∪ {encCall (d.hd m)} := by
  rw [prec_trStripsDom hn, hget, specOf_beg, begSpec, if_pos hm]
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

theorem add_beg (hn : n < (cacts d).length) (hget : (cacts d).getI n = (0, i, m, j, m'))
    (hm : m < d.methods.length) :
    (trStripsDom d).add n = stSet ∅ ∪ {encCur 0 m 0} := by
  rw [add_trStripsDom hn, hget, specOf_beg, begSpec, if_pos hm]
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

theorem del_beg (hn : n < (cacts d).length) (hget : (cacts d).getI n = (0, i, m, j, m'))
    (hm : m < d.methods.length) :
    (trStripsDom d).del n = stSet ∅ ∪ {encCall (d.hd m)} := by
  rw [del_trStripsDom hn, hget, specOf_beg, begSpec, if_pos hm]
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

theorem specOf_beg_invalid (hget : (cacts d).getI n = (0, i, m, j, m'))
    (hm : ¬ m < d.methods.length) : specOf d ((cacts d).getI n) = badSpec := by
  rw [hget, specOf_beg, begSpec, if_neg hm]

end Beg

section Exec

variable {n i m j m' a : ℕ}

theorem execSpec_of_valid (hval : (d.bd m)[j]? = some (Sum.inl a)) :
    execSpec d i m j =
      (encCur i m j :: (d.precList a).map encSt, encCur i m (j + 1) :: (d.addList a).map encSt,
        encCur i m j :: (d.delList a).map encSt) := by
  have hj : j < (d.bd m).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hval
    exact absurd hval (by simp)
  obtain ⟨hcomp, hact⟩ := (DomDesc.isCompAt_false_iff hj).2 hval
  rw [execSpec, if_pos ⟨hj, hcomp⟩, hact]

theorem prec_exec (hn : n < (cacts d).length) (hget : (cacts d).getI n = (1, i, m, j, m'))
    (hval : (d.bd m)[j]? = some (Sum.inl a)) :
    (trStripsDom d).prec n = stSet (d.prec a) ∪ {encCur i m j} := by
  rw [prec_trStripsDom hn, hget, specOf_exec, execSpec_of_valid hval]
  rw [setOf_mem_cons_map, DomDesc.prec_eq]

theorem add_exec (hn : n < (cacts d).length) (hget : (cacts d).getI n = (1, i, m, j, m'))
    (hval : (d.bd m)[j]? = some (Sum.inl a)) :
    (trStripsDom d).add n = stSet (d.add a) ∪ {encCur i m (j + 1)} := by
  rw [add_trStripsDom hn, hget, specOf_exec, execSpec_of_valid hval]
  rw [setOf_mem_cons_map, DomDesc.add_eq]

theorem del_exec (hn : n < (cacts d).length) (hget : (cacts d).getI n = (1, i, m, j, m'))
    (hval : (d.bd m)[j]? = some (Sum.inl a)) :
    (trStripsDom d).del n = stSet (d.del a) ∪ {encCur i m j} := by
  rw [del_trStripsDom hn, hget, specOf_exec, execSpec_of_valid hval]
  rw [setOf_mem_cons_map, DomDesc.del_eq]

theorem specOf_exec_invalid (hget : (cacts d).getI n = (1, i, m, j, m'))
    (hval : ∀ b, (d.bd m)[j]? ≠ some (Sum.inl b)) : specOf d ((cacts d).getI n) = badSpec := by
  rw [hget, specOf_exec, execSpec]
  refine if_neg ?_
  rintro ⟨hj, hcomp⟩
  exact hval (d.actAt m j) ((DomDesc.isCompAt_false_iff hj).1 ⟨hcomp, rfl⟩)

end Exec

section Push

variable {n i m j m' c : ℕ}

theorem pushSpec_of_valid (hval : (d.bd m)[j]? = some (Sum.inr c)) (hc : d.hd m' = c)
    (hlast : j + 1 < (d.bd m).length) (hm' : m' < d.methods.length)
    (hi : i + 1 < d.methods.length) :
    pushSpec d i m j m' =
      ([encCur i m j], [encCur (i + 1) m' 0, encSav i m (j + 1)], [encCur i m j]) := by
  have hj : j < (d.bd m).length := by omega
  obtain ⟨hcomp, hcc⟩ := (DomDesc.isCompAt_true_iff hj).2 hval
  rw [pushSpec, if_pos ⟨hlast, hcomp, by rw [hcc, hc], hm', hi⟩]

theorem prec_push (hn : n < (cacts d).length) (hget : (cacts d).getI n = (2, i, m, j, m'))
    (hval : (d.bd m)[j]? = some (Sum.inr c)) (hc : d.hd m' = c)
    (hlast : j + 1 < (d.bd m).length) (hm' : m' < d.methods.length)
    (hi : i + 1 < d.methods.length) :
    (trStripsDom d).prec n = stSet ∅ ∪ {encCur i m j} := by
  rw [prec_trStripsDom hn, hget, specOf_push, pushSpec_of_valid hval hc hlast hm' hi]
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

theorem add_push (hn : n < (cacts d).length) (hget : (cacts d).getI n = (2, i, m, j, m'))
    (hval : (d.bd m)[j]? = some (Sum.inr c)) (hc : d.hd m' = c)
    (hlast : j + 1 < (d.bd m).length) (hm' : m' < d.methods.length)
    (hi : i + 1 < d.methods.length) :
    (trStripsDom d).add n = stSet ∅ ∪ {encCur (i + 1) m' 0, encSav i m (j + 1)} := by
  rw [add_trStripsDom hn, hget, specOf_push, pushSpec_of_valid hval hc hlast hm' hi]
  simp only [setOf_mem_pair, stSet_empty, Set.empty_union]

theorem del_push (hn : n < (cacts d).length) (hget : (cacts d).getI n = (2, i, m, j, m'))
    (hval : (d.bd m)[j]? = some (Sum.inr c)) (hc : d.hd m' = c)
    (hlast : j + 1 < (d.bd m).length) (hm' : m' < d.methods.length)
    (hi : i + 1 < d.methods.length) :
    (trStripsDom d).del n = stSet ∅ ∪ {encCur i m j} := by
  rw [del_trStripsDom hn, hget, specOf_push, pushSpec_of_valid hval hc hlast hm' hi]
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

/-- The parameters of a `push` action that is not unsatisfiable. -/
theorem push_valid_of_ne_bad (hget : (cacts d).getI n = (2, i, m, j, m'))
    (h : specOf d ((cacts d).getI n) ≠ badSpec) :
    (d.bd m)[j]? = some (Sum.inr (d.hd m')) ∧ j + 1 < (d.bd m).length ∧
      m' < d.methods.length ∧ i + 1 < d.methods.length := by
  rw [hget, specOf_push, pushSpec] at h
  by_cases hcond : j + 1 < (d.bd m).length ∧ d.isCompAt m j = true ∧ d.compAt m j = d.hd m' ∧
      m' < d.methods.length ∧ i + 1 < d.methods.length
  · obtain ⟨hlast, hcomp, hcc, hm', hi⟩ := hcond
    exact ⟨(DomDesc.isCompAt_true_iff (by omega)).1 ⟨hcomp, hcc⟩, hlast, hm', hi⟩
  · exact absurd (if_neg hcond) h

end Push

section Tail

variable {n i m j m' c : ℕ}

theorem tailSpec_of_valid (hval : (d.bd m)[j]? = some (Sum.inr c)) (hc : d.hd m' = c)
    (hlast : j + 1 = (d.bd m).length) (hm' : m' < d.methods.length) :
    tailSpec d i m j m' = ([encCur i m j], [encCur i m' 0], [encCur i m j]) := by
  have hj : j < (d.bd m).length := by omega
  obtain ⟨hcomp, hcc⟩ := (DomDesc.isCompAt_true_iff hj).2 hval
  rw [tailSpec, if_pos ⟨hlast, hcomp, by rw [hcc, hc], hm'⟩]

theorem prec_tail (hn : n < (cacts d).length) (hget : (cacts d).getI n = (3, i, m, j, m'))
    (hval : (d.bd m)[j]? = some (Sum.inr c)) (hc : d.hd m' = c)
    (hlast : j + 1 = (d.bd m).length) (hm' : m' < d.methods.length) :
    (trStripsDom d).prec n = stSet ∅ ∪ {encCur i m j} := by
  rw [prec_trStripsDom hn, hget, specOf_tail, tailSpec_of_valid hval hc hlast hm']
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

theorem add_tail (hn : n < (cacts d).length) (hget : (cacts d).getI n = (3, i, m, j, m'))
    (hval : (d.bd m)[j]? = some (Sum.inr c)) (hc : d.hd m' = c)
    (hlast : j + 1 = (d.bd m).length) (hm' : m' < d.methods.length) :
    (trStripsDom d).add n = stSet ∅ ∪ {encCur i m' 0} := by
  rw [add_trStripsDom hn, hget, specOf_tail, tailSpec_of_valid hval hc hlast hm']
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

theorem del_tail (hn : n < (cacts d).length) (hget : (cacts d).getI n = (3, i, m, j, m'))
    (hval : (d.bd m)[j]? = some (Sum.inr c)) (hc : d.hd m' = c)
    (hlast : j + 1 = (d.bd m).length) (hm' : m' < d.methods.length) :
    (trStripsDom d).del n = stSet ∅ ∪ {encCur i m j} := by
  rw [del_trStripsDom hn, hget, specOf_tail, tailSpec_of_valid hval hc hlast hm']
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

/-- The parameters of a `tail` action that is not unsatisfiable. -/
theorem tail_valid_of_ne_bad (hget : (cacts d).getI n = (3, i, m, j, m'))
    (h : specOf d ((cacts d).getI n) ≠ badSpec) :
    (d.bd m)[j]? = some (Sum.inr (d.hd m')) ∧ j + 1 = (d.bd m).length ∧
      m' < d.methods.length := by
  rw [hget, specOf_tail, tailSpec] at h
  by_cases hcond : j + 1 = (d.bd m).length ∧ d.isCompAt m j = true ∧ d.compAt m j = d.hd m' ∧
      m' < d.methods.length
  · obtain ⟨hlast, hcomp, hcc, hm'⟩ := hcond
    exact ⟨(DomDesc.isCompAt_true_iff (by omega)).1 ⟨hcomp, hcc⟩, hlast, hm'⟩
  · exact absurd (if_neg hcond) h

end Tail

section Ret

variable {n i m j' m' : ℕ}

theorem prec_ret (hn : n < (cacts d).length) (hget : (cacts d).getI n = (4, i, m, j', m'))
    (hi : 0 < i) :
    (trStripsDom d).prec n =
      stSet ∅ ∪ {encCur i m (d.bd m).length, encSav (i - 1) m' j'} := by
  rw [prec_trStripsDom hn, hget, specOf_ret, retSpec, if_pos hi]
  simp only [setOf_mem_pair, stSet_empty, Set.empty_union]

theorem add_ret (hn : n < (cacts d).length) (hget : (cacts d).getI n = (4, i, m, j', m'))
    (hi : 0 < i) :
    (trStripsDom d).add n = stSet ∅ ∪ {encCur (i - 1) m' j'} := by
  rw [add_trStripsDom hn, hget, specOf_ret, retSpec, if_pos hi]
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

theorem del_ret (hn : n < (cacts d).length) (hget : (cacts d).getI n = (4, i, m, j', m'))
    (hi : 0 < i) :
    (trStripsDom d).del n =
      stSet ∅ ∪ {encCur i m (d.bd m).length, encSav (i - 1) m' j'} := by
  rw [del_trStripsDom hn, hget, specOf_ret, retSpec, if_pos hi]
  simp only [setOf_mem_pair, stSet_empty, Set.empty_union]

theorem specOf_ret_invalid (hget : (cacts d).getI n = (4, i, m, j', m')) (hi : ¬ 0 < i) :
    specOf d ((cacts d).getI n) = badSpec := by
  rw [hget, specOf_ret, retSpec, if_neg hi]

end Ret

section Fin

variable {n i m j m' : ℕ}

theorem prec_fin (hn : n < (cacts d).length) (hget : (cacts d).getI n = (5, i, m, j, m')) :
    (trStripsDom d).prec n = stSet ∅ ∪ {encCur 0 m (d.bd m).length} := by
  rw [prec_trStripsDom hn, hget, specOf_fin, finSpec]
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

theorem add_fin (hn : n < (cacts d).length) (hget : (cacts d).getI n = (5, i, m, j, m')) :
    (trStripsDom d).add n = stSet ∅ ∪ {encDone} := by
  rw [add_trStripsDom hn, hget, specOf_fin, finSpec]
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

theorem del_fin (hn : n < (cacts d).length) (hget : (cacts d).getI n = (5, i, m, j, m')) :
    (trStripsDom d).del n = stSet ∅ ∪ {encCur 0 m (d.bd m).length} := by
  rw [del_trStripsDom hn, hget, specOf_fin, finSpec]
  simp only [setOf_mem_singleton, stSet_empty, Set.empty_union]

end Fin

/-! ### Applicability and transitions, in terms of the split of a state -/

theorem applicable_gen {n : ℕ} {P Cp : Set ℕ} (hprec : (trStripsDom d).prec n = stSet P ∪ Cp)
    (hCp : ∀ x ∈ Cp, x % 6 ≠ 0) (s : Set ℕ) (C : Set ℕ) (hC : ∀ x ∈ C, x % 6 ≠ 0) :
    (trStripsDom d).toDomain.Applicable n (stSet s ∪ C) ↔ P ⊆ s ∧ Cp ⊆ C := by
  show (trStripsDom d).prec n ⊆ _ ↔ _
  rw [hprec]
  exact subset_cfg_iff hCp hC

theorem transition_gen {n : ℕ} {D A Cdel Cadd : Set ℕ}
    (hdel : (trStripsDom d).del n = stSet D ∪ Cdel)
    (hadd : (trStripsDom d).add n = stSet A ∪ Cadd)
    (hCdel : ∀ x ∈ Cdel, x % 6 ≠ 0) (hCadd : ∀ x ∈ Cadd, x % 6 ≠ 0) (s : Set ℕ) (C : Set ℕ)
    (hC : ∀ x ∈ C, x % 6 ≠ 0) :
    (trStripsDom d).toDomain.transition n (stSet s ∪ C)
      = stSet ((s \ D) ∪ A) ∪ ((C \ Cdel) ∪ Cadd) := by
  show ((stSet s ∪ C) \ (trStripsDom d).del n) ∪ (trStripsDom d).add n = _
  rw [hdel, hadd]
  exact transition_split s D A C Cdel Cadd hC hCdel hCadd

/-! ### The three shapes of a state -/

theorem cfg_eq (s : Set ℕ) (st : List (ℕ × ℕ)) : cfg s st = stSet s ∪ ctlSet st := rfl

theorem endCfg_eq (s : Set ℕ) : endCfg s = stSet s ∪ {encDone} := by
  rw [endCfg]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
  tauto

theorem startCfg_eq (s : Set ℕ) (c : ℕ) : startCfg s c = stSet s ∪ {encCall c} := by
  rw [startCfg]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
  tauto

theorem mod_ne_zero_endCfg : ∀ x ∈ ({encDone} : Set ℕ), x % 6 ≠ 0 := by
  rintro x rfl; simp [encDone]

theorem mod_ne_zero_startCfg (c : ℕ) : ∀ x ∈ ({encCall c} : Set ℕ), x % 6 ≠ 0 := by
  rintro x rfl; simp

theorem mod_ne_zero_cur (i m j : ℕ) : ∀ x ∈ ({encCur i m j} : Set ℕ), x % 6 ≠ 0 := by
  rintro x rfl; simp

theorem mod_ne_zero_pair_cur_sav (i m j i' m' j' : ℕ) :
    ∀ x ∈ ({encCur i m j, encSav i' m' j'} : Set ℕ), x % 6 ≠ 0 := by
  rintro x (rfl | rfl) <;> simp

theorem mod_ne_zero_empty : ∀ x ∈ (∅ : Set ℕ), x % 6 ≠ 0 := by
  rintro x ⟨⟩

theorem encBot_notMem_cfg (s : Set ℕ) (st : List (ℕ × ℕ)) : encBot ∉ cfg s st := by
  rintro (h | h)
  · exact absurd (mod_zero_of_mem_stSet h) (by simp)
  · rcases mod_of_mem_ctlSet h with h' | h' <;> simp [encBot] at h'

theorem encBot_notMem_endCfg (s : Set ℕ) : encBot ∉ endCfg s := by
  rw [endCfg_eq]
  rintro (h | h)
  · exact absurd (mod_zero_of_mem_stSet h) (by simp)
  · simp only [Set.mem_singleton_iff] at h
    simp [encBot, encDone] at h

theorem encBot_notMem_startCfg (s : Set ℕ) (c : ℕ) : encBot ∉ startCfg s c := by
  rw [startCfg_eq]
  rintro (h | h)
  · exact absurd (mod_zero_of_mem_stSet h) (by simp)
  · simp only [Set.mem_singleton_iff] at h
    exact absurd (congrArg (· % 6) h) (by simp)

theorem encDone_notMem_cfg (s : Set ℕ) (st : List (ℕ × ℕ)) : encDone ∉ cfg s st := by
  rintro (h | h)
  · exact absurd (mod_zero_of_mem_stSet h) (by simp)
  · rcases mod_of_mem_ctlSet h with h' | h' <;> simp [encDone] at h'

theorem encDone_notMem_startCfg (s : Set ℕ) (c : ℕ) : encDone ∉ startCfg s c := by
  rw [startCfg_eq]
  rintro (h | h)
  · exact absurd (mod_zero_of_mem_stSet h) (by simp)
  · simp only [Set.mem_singleton_iff] at h
    exact absurd (congrArg (· % 6) h) (by simp [encDone])

end Syn

end HTN
