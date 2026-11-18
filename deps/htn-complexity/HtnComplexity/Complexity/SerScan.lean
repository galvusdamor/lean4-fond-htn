import ComplexityTheory.Complexity.CobhamString
import HtnComplexity.Complexity.Serial
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Recognising the layers of the serialisation

The serialisation of `HtnComplexity/Complexity/Serial.lean` has two layers: a bit string
written self-delimitingly (`HTN.Syn.bstr`), and a list of such strings (`HTN.Syn.blist`).  Reading
a description off its code needs to *locate* those layers inside the code, and this file provides
the three tests that do it, each of them a finite-state scan and therefore a predicate of Cobham's
class (`ComplexityTheory/Complexity/CobhamDFA.lean`):

* `HTN.Syn.blistB u` — is `u` a serialised list, `u = blist l`?
* `HTN.Syn.entriesB u` — is `u` a *sequence of complete entries*, `u = entriesEnc l`?  This is a
  `blist` without its terminating `false`, and it is what a prefix of a `blist` that stops at an
  entry boundary looks like;
* `HTN.Syn.entryB u` — is `u` exactly one entry, `u = true :: bstr w`?

The three characterisations (`HTN.Syn.blistB_iff`, `…entriesB_iff`, `…entryB_iff`) turn the scans
into statements about the serialisation, and, with the prefix-freeness of the two layers
(`HTN.Syn.bstr_parse`, `HTN.Syn.blist_parse`), that is all that is needed to pin down the position
of a sublist inside a code: a prefix of a code that is a complete `blist` *is* the first list of
the code.
-/

namespace HTN

namespace Syn

open PTime

/-! ### Sequences of complete entries -/

/-- A list of bit strings written as a sequence of complete entries: the serialisation
`HTN.Syn.blist` without its terminating `false`. -/
def entriesEnc (l : List (List Bool)) : List Bool := l.flatMap fun x => true :: bstr x

@[simp] theorem entriesEnc_nil : entriesEnc [] = [] := rfl

theorem entriesEnc_cons (x : List Bool) (l : List (List Bool)) :
    entriesEnc (x :: l) = true :: (bstr x ++ entriesEnc l) := by
  simp [entriesEnc]

theorem blist_eq_entriesEnc (l : List (List Bool)) : blist l = entriesEnc l ++ [false] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [blist_cons, entriesEnc_cons, ih]

/-- Strong induction on the length of a bit string. -/
theorem strongLenRec {P : List Bool → Prop}
    (ind : ∀ u, (∀ v : List Bool, v.length < u.length → P v) → P u) (u : List Bool) : P u := by
  have key : ∀ n u, u.length ≤ n → P u := by
    intro n
    induction n with
    | zero => exact fun u hu => ind u fun v hv => absurd hv (by omega)
    | succ n ih => exact fun u hu => ind u fun v hv => ih v (by omega)
  exact key u.length u le_rfl

/-! ### The scan of the two layers -/

/-- The states of the scan that parses a `blist`. -/
inductive ScanSt
  | atEntry
  | inPair
  | afterMark
  | fin
  | dead
  deriving DecidableEq, Repr

open ScanSt

/-- The transition of the scan.  At an entry boundary, `true` starts an entry and `false` is the
terminator of the list; inside an entry, `true` starts a pair and `false` ends the entry; after a
pair marker the next character is a data bit. -/
def scanStep : ScanSt → Bool → ScanSt
  | atEntry, true => inPair
  | atEntry, false => fin
  | inPair, true => afterMark
  | inPair, false => atEntry
  | afterMark, _ => inPair
  | fin, _ => dead
  | dead, _ => dead

theorem scanStep_dead (b : Bool) : scanStep dead b = dead := by cases b <;> rfl

theorem foldl_dead (u : List Bool) : u.foldl scanStep dead = dead := by
  induction u with
  | nil => rfl
  | cons b u ih => rw [List.foldl_cons, scanStep_dead]; exact ih

theorem foldl_fin (u : List Bool) :
    u.foldl scanStep fin = if u = [] then fin else dead := by
  cases u with
  | nil => rfl
  | cons b u =>
    rw [List.foldl_cons, show scanStep fin b = dead from by cases b <;> rfl, foldl_dead]
    simp

/-- Running the scan through one self-delimiting string, from a pair boundary. -/
theorem foldl_bstr (x u : List Bool) :
    (bstr x ++ u).foldl scanStep inPair = u.foldl scanStep atEntry := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    rw [bstr_cons]
    show (true :: b :: (bstr x ++ u)).foldl scanStep inPair = _
    rw [List.foldl_cons, List.foldl_cons]
    have h1 : scanStep inPair true = afterMark := rfl
    have h2 : scanStep afterMark b = inPair := by cases b <;> rfl
    rw [h1, h2, ih]

/-- Running the scan through a sequence of complete entries. -/
theorem foldl_entriesEnc (l : List (List Bool)) (u : List Bool) :
    (entriesEnc l ++ u).foldl scanStep atEntry = u.foldl scanStep atEntry := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [entriesEnc_cons]
    show (true :: (bstr x ++ entriesEnc l ++ u)).foldl scanStep atEntry = _
    rw [List.foldl_cons, show scanStep atEntry true = inPair from rfl, List.append_assoc,
      foldl_bstr, ih]

/-- The scan, started inside an entry, can only reach an entry boundary or the end of the list by
reading a complete self-delimiting string first. -/
theorem inPair_split (t : ScanSt) (ht : t = atEntry ∨ t = fin) :
    ∀ u : List Bool, u.foldl scanStep inPair = t →
      ∃ x w, u = bstr x ++ w ∧ w.foldl scanStep atEntry = t := by
  intro u
  induction u using strongLenRec with
  | ind u ih =>
    match u with
    | [] =>
      intro h
      rcases ht with rfl | rfl <;> simp at h
    | false :: u' =>
      intro h
      refine ⟨[], u', by simp, ?_⟩
      rwa [List.foldl_cons, show scanStep inPair false = atEntry from rfl] at h
    | true :: [] =>
      intro h
      rcases ht with rfl | rfl <;> simp [scanStep] at h
    | true :: b :: u'' =>
      intro h
      have h' : u''.foldl scanStep inPair = t := by
        rw [List.foldl_cons, List.foldl_cons, show scanStep inPair true = afterMark from rfl,
          show scanStep afterMark b = inPair from by cases b <;> rfl] at h
        exact h
      obtain ⟨x, w, hx, hw⟩ := ih u'' (by simp) h'
      exact ⟨b :: x, w, by rw [bstr_cons, hx]; rfl, hw⟩

/-! ### The three tests -/

/-- Is the string a sequence of complete entries? -/
def entriesB (u : List Bool) : Bool := u.foldl scanStep atEntry == atEntry

/-- Is the string a serialised list of bit strings? -/
def blistB (u : List Bool) : Bool := u.foldl scanStep atEntry == fin

/-- The scan reaches an entry boundary exactly on a sequence of complete entries. -/
theorem atEntry_split : ∀ u : List Bool, u.foldl scanStep atEntry = atEntry →
    ∃ l, u = entriesEnc l := by
  intro u
  induction u using strongLenRec with
  | ind u ih =>
    match u with
    | [] => exact fun _ => ⟨[], rfl⟩
    | false :: u' =>
      intro h
      rw [List.foldl_cons, show scanStep atEntry false = fin from rfl, foldl_fin] at h
      split at h <;> simp at h
    | true :: u'' =>
      intro h
      rw [List.foldl_cons, show scanStep atEntry true = inPair from rfl] at h
      obtain ⟨x, w, hx, hw⟩ := inPair_split atEntry (Or.inl rfl) u'' h
      have hlt : w.length < (true :: u'').length := by
        rw [hx]
        simp
      obtain ⟨l, hl⟩ := ih w hlt hw
      exact ⟨x :: l, by rw [entriesEnc_cons, hx, hl]⟩

/-- The scan reaches the end of the list exactly on a serialised list. -/
theorem atEntry_fin_split : ∀ u : List Bool, u.foldl scanStep atEntry = fin →
    ∃ l, u = blist l := by
  intro u
  induction u using strongLenRec with
  | ind u ih =>
    match u with
    | [] => intro h; simp at h
    | false :: u' =>
      intro h
      rw [List.foldl_cons, show scanStep atEntry false = fin from rfl, foldl_fin] at h
      split at h
      · next hu => exact ⟨[], by rw [hu]; rfl⟩
      · simp at h
    | true :: u'' =>
      intro h
      rw [List.foldl_cons, show scanStep atEntry true = inPair from rfl] at h
      obtain ⟨x, w, hx, hw⟩ := inPair_split fin (Or.inr rfl) u'' h
      have hlt : w.length < (true :: u'').length := by
        rw [hx]
        simp
      obtain ⟨l, hl⟩ := ih w hlt hw
      exact ⟨x :: l, by rw [blist_cons, hx, hl]⟩

theorem entriesB_iff {u : List Bool} : entriesB u = true ↔ ∃ l, u = entriesEnc l := by
  constructor
  · intro h
    exact atEntry_split u (by simpa [entriesB] using h)
  · rintro ⟨l, rfl⟩
    have h := foldl_entriesEnc l []
    simp only [List.append_nil] at h
    simp [entriesB, h]

theorem blistB_iff {u : List Bool} : blistB u = true ↔ ∃ l, u = blist l := by
  constructor
  · intro h
    exact atEntry_fin_split u (by simpa [blistB] using h)
  · rintro ⟨l, rfl⟩
    have h : (blist l).foldl scanStep atEntry = fin := by
      rw [blist_eq_entriesEnc, foldl_entriesEnc]
      rfl
    simp [blistB, h]

/-! ### One entry -/

/-- The states of the scan that recognises a single entry. -/
inductive EntSt
  | start
  | inPair
  | afterMark
  | fin
  | dead
  deriving DecidableEq, Repr

/-- The transition of the single-entry scan. -/
def entStep : EntSt → Bool → EntSt
  | EntSt.start, true => EntSt.inPair
  | EntSt.start, false => EntSt.dead
  | EntSt.inPair, true => EntSt.afterMark
  | EntSt.inPair, false => EntSt.fin
  | EntSt.afterMark, _ => EntSt.inPair
  | EntSt.fin, _ => EntSt.dead
  | EntSt.dead, _ => EntSt.dead

theorem entFoldl_dead (u : List Bool) : u.foldl entStep EntSt.dead = EntSt.dead := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    rw [List.foldl_cons, show entStep EntSt.dead b = EntSt.dead from by cases b <;> rfl]
    exact ih

theorem entFoldl_fin (u : List Bool) :
    u.foldl entStep EntSt.fin = if u = [] then EntSt.fin else EntSt.dead := by
  cases u with
  | nil => rfl
  | cons b u =>
    rw [List.foldl_cons, show entStep EntSt.fin b = EntSt.dead from by cases b <;> rfl,
      entFoldl_dead]
    simp

theorem entFoldl_bstr (x u : List Bool) :
    (bstr x ++ u).foldl entStep EntSt.inPair = u.foldl entStep EntSt.fin := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    rw [bstr_cons]
    show (true :: b :: (bstr x ++ u)).foldl entStep EntSt.inPair = _
    rw [List.foldl_cons, List.foldl_cons,
      show entStep EntSt.inPair true = EntSt.afterMark from rfl,
      show entStep EntSt.afterMark b = EntSt.inPair from by cases b <;> rfl, ih]

theorem entInPair_split : ∀ u : List Bool, u.foldl entStep EntSt.inPair = EntSt.fin →
    ∃ x, u = bstr x := by
  intro u
  induction u using strongLenRec with
  | ind u ih =>
    match u with
    | [] => intro h; simp at h
    | false :: u' =>
      intro h
      rw [List.foldl_cons, show entStep EntSt.inPair false = EntSt.fin from rfl,
        entFoldl_fin] at h
      split at h
      · next hu => exact ⟨[], by rw [hu]; rfl⟩
      · simp at h
    | true :: [] => intro h; simp [entStep] at h
    | true :: b :: u'' =>
      intro h
      have h' : u''.foldl entStep EntSt.inPair = EntSt.fin := by
        rw [List.foldl_cons, List.foldl_cons,
          show entStep EntSt.inPair true = EntSt.afterMark from rfl,
          show entStep EntSt.afterMark b = EntSt.inPair from by cases b <;> rfl] at h
        exact h
      obtain ⟨x, hx⟩ := ih u'' (by simp) h'
      exact ⟨b :: x, by rw [bstr_cons, hx]⟩

/-- Is the string exactly one entry? -/
def entryB (u : List Bool) : Bool := u.foldl entStep EntSt.start == EntSt.fin

theorem entryB_iff {u : List Bool} : entryB u = true ↔ ∃ w, u = true :: bstr w := by
  constructor
  · intro h
    have h' : u.foldl entStep EntSt.start = EntSt.fin := by simpa [entryB] using h
    match u with
    | [] => simp at h'
    | false :: u' =>
      rw [List.foldl_cons, show entStep EntSt.start false = EntSt.dead from rfl,
        entFoldl_dead] at h'
      simp at h'
    | true :: u'' =>
      rw [List.foldl_cons, show entStep EntSt.start true = EntSt.inPair from rfl] at h'
      obtain ⟨x, hx⟩ := entInPair_split u'' h'
      exact ⟨x, by rw [hx]⟩
  · rintro ⟨w, rfl⟩
    have h := entFoldl_bstr w []
    simp only [List.append_nil] at h
    rw [entryB]
    rw [List.foldl_cons, show entStep EntSt.start true = EntSt.inPair from rfl, h]
    rfl

/-! ### The three tests are predicates of Cobham's class -/

theorem cobhamB_of_dfa {σ : Type} [DecidableEq σ] (states : List σ) (init : σ)
    (step : σ → Bool → σ) (out : σ → Bool) (hinit : init ∈ states)
    (hstep : ∀ s b, s ∈ states → step s b ∈ states) {a : Fn} (ha : Cobham a) :
    CobhamB fun args => out ((a args).foldl step init) := by
  obtain ⟨f, hf, hfa⟩ := (polyTimeFun_dfaFoldl states init step out hinit hstep).cobham
  refine (cobham_c1 hf ha).of_eq' fun args => ?_
  show f [a args] = _
  rw [← hfa (a args)]

theorem cobhamB_entriesB {a : Fn} (ha : Cobham a) : CobhamB fun args => entriesB (a args) :=
  cobhamB_of_dfa [ScanSt.atEntry, ScanSt.inPair, ScanSt.afterMark, ScanSt.fin, ScanSt.dead]
    ScanSt.atEntry scanStep (fun s => s == ScanSt.atEntry) (by simp)
    (by
      intro s b _
      cases s <;> cases b <;> simp [scanStep]) ha

theorem cobhamB_blistB {a : Fn} (ha : Cobham a) : CobhamB fun args => blistB (a args) :=
  cobhamB_of_dfa [ScanSt.atEntry, ScanSt.inPair, ScanSt.afterMark, ScanSt.fin, ScanSt.dead]
    ScanSt.atEntry scanStep (fun s => s == ScanSt.fin) (by simp)
    (by
      intro s b _
      cases s <;> cases b <;> simp [scanStep]) ha

theorem cobhamB_entryB {a : Fn} (ha : Cobham a) : CobhamB fun args => entryB (a args) :=
  cobhamB_of_dfa [EntSt.start, EntSt.inPair, EntSt.afterMark, EntSt.fin, EntSt.dead]
    EntSt.start entStep (fun s => s == EntSt.fin) (by simp)
    (by
      intro s b _
      cases s <;> cases b <;> simp [entStep]) ha

end Syn

end HTN
