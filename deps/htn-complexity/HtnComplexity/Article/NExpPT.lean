import HtnComplexity.Article.NExpRendU
import HtnComplexity.Article.StripsTM
/-!
# The acyclic encoding of Thm. 4.3.7 is computed in polynomial time

For a machine `N` with states `Fin k` over `TapeSym`, the normalised machine
`HTN.TMEnc.homingMachine N` has states `Fin k ⊕ Bool` and symbols `TapeSym × Bool`, numbered by
`HTN.TMEnc.U.qN` and `HTN.TMEnc.U.gN`.  The listed methods of the rendering
`HTN.TMEnc.U.rendU`, numbered (`HTN.TMEnc.U.encB`), are computed in polynomial time from the
word and the time bound `K` in binary (`HTN.TMEnc.U.pt_methodsN`).

Functions of finite arguments are polynomial time by table lookup (`HTN.TMEnc.U.pt_of_finite`).
-/

namespace HTN

namespace TMEnc

namespace U

open scoped Classical

open TM Syn Syn.PolyDom PTime Article

/-! ### Functions of finite arguments -/

section Fin

theorem pt_of_list {β γ : Type} [BEnc β] [BEnc γ] [DecidableEq β] (f : β → γ) (d : β) :
    ∀ l : List β, PT fun b => l.foldr (fun e acc => if b = e then f e else acc) (f d)
  | [] => PT.const _
  | e :: l => (PT.ite (PT.eq PT.id (PT.const e)) (PT.const (f e)) (pt_of_list f d l)).of_eq
      fun b => rfl

/-- **A function of a finite argument is polynomial time.** -/
theorem pt_of_finite {β γ : Type} [BEnc β] [BEnc γ] [DecidableEq β] [Fintype β] [Inhabited β]
    (f : β → γ) : PT f := by
  refine (pt_of_list f default (Finset.univ : Finset β).toList).of_eq fun b => ?_
  have : ∀ l : List β, b ∈ l →
      l.foldr (fun e acc => if b = e then f e else acc) (f default) = f b := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons e l ih =>
      intro h
      by_cases he : b = e
      · simp [he]
      · simp only [List.foldr_cons, if_neg he]
        exact ih (by simpa [he] using h)
  exact this _ (by simp)

end Fin

/-! ### The numberings of the normalised machine -/

/-- The states of the normalised machine. -/
abbrev QH (k : ℕ) : Type := Fin k ⊕ Bool

/-- The symbols of the normalised machine. -/
abbrev GH : Type := Option Bool × Bool

def qN {k : ℕ} : QH k → ℕ
  | Sum.inl i => 2 * i.val
  | Sum.inr b => 2 * b.toNat + 1

def gN (c : GH) : ℕ := 2 * symCode c.1 + c.2.toNat

theorem qN_injective {k : ℕ} : Function.Injective (qN (k := k)) := by
  rintro (i | b) (j | c) h <;> simp only [qN] at h
  · exact congrArg _ (Fin.ext (by omega))
  · cases c <;> simp at h <;> omega
  · cases b <;> simp at h <;> omega
  · cases b <;> cases c <;> simp_all

theorem gN_injective : Function.Injective gN := by
  rintro ⟨o, b⟩ ⟨o', b'⟩ h
  simp only [gN] at h
  have := symCode_lt o
  have := symCode_lt o'
  have h1 : symCode o = symCode o' := by cases b <;> cases b' <;> simp at h <;> omega
  have h2 : b = b' := by cases b <;> cases b' <;> simp_all
  rw [symCode_inj h1, h2]

variable {k : ℕ}

/-- The numbered label of a cell. -/
def labH (x : TMAct (QH k) GH ⊕ TMTask (QH k) GH) : Bool × ℕ := encLabel (encTMAct qN gN) (encTMTask gN) x

/-- A numbered method. -/
def encB (p : TMTask (QH k) GH × Body (QH k) GH) : ℕ × List (List (Bool × ℕ)) :=
  (encTMTask gN p.1, p.2.map (·.map labH))

/-! ### Polynomial time of the pieces -/

section Pieces

variable {α : Type} [BEnc α]

theorem pt_eT_cSeq (t : TMTask (QH k) GH) {f : α → ℕ} (hf : PT f) :
    PT fun a => encTMTask gN (TMTask.cSeq t (f a)) :=
  (PT.affine 20 17 (PT.natPair (PT.const _) hf)).of_eq fun _ => rfl

theorem pt_eT_cPar (t : TMTask (QH k) GH) {f : α → ℕ} (hf : PT f) :
    PT fun a => encTMTask gN (TMTask.cPar t (f a)) :=
  (PT.affine 20 18 (PT.natPair (PT.const _) hf)).of_eq fun _ => rfl

theorem pt_eT_cParW {j f : α → ℕ} (hj : PT j) (hf : PT f) :
    PT fun a => encTMTask (Q := QH k) gN (TMTask.cPar (TMTask.waitN (j a)) (f a)) :=
  (PT.affine 20 18 (PT.natPair (PT.affine 20 6 hj) hf)).of_eq fun _ => rfl

theorem pt_eT_waitN {f : α → ℕ} (hf : PT f) :
    PT fun a => encTMTask (Q := QH k) gN (TMTask.waitN (f a)) :=
  (PT.affine 20 6 hf).of_eq fun _ => rfl

theorem pt_eT_checkers {f : α → ℕ} (hf : PT f) :
    PT fun a => encTMTask (Q := QH k) gN (TMTask.checkers (f a)) :=
  (PT.affine 20 13 hf).of_eq fun _ => rfl

theorem pt_eT_produceWord {f : α → ℕ} (hf : PT f) :
    PT fun a => encTMTask (Q := QH k) gN (TMTask.produceWord (f a)) :=
  (PT.affine 20 15 hf).of_eq fun _ => rfl

theorem pt_lab_inr {t : α → TMTask (QH k) GH} (ht : PT fun a => encTMTask gN (t a)) :
    PT fun a => labH (Sum.inr (t a)) :=
  PT.pair (PT.const true) ht

theorem pt_lab_inl {β : Type} [BEnc β] [DecidableEq β] [Fintype β] [Inhabited β]
    (F : β → TMAct (QH k) GH) {g : α → β} (hg : PT g) : PT fun a => labH (Sum.inl (F (g a))) :=
  (pt_of_finite fun b => labH (Sum.inl (F b))).comp hg

end Pieces

/-! ### Numeric forms of the bodies -/

section Numeric

/-- The counting body, numbered. -/
def seqN (tc j : ℕ) : List (List (Bool × ℕ)) :=
  if j = 0 then [] else if j = 1 then [[(true, tc)]]
  else if j % 2 = 0 then [[(true, 20 * Nat.pair tc (j / 2) + 17), (true, 20 * Nat.pair tc (j / 2) + 17)]]
  else [[(true, tc), (true, 20 * Nat.pair tc (j - 1) + 17)]]

def parN (tc j : ℕ) : List (List (Bool × ℕ)) :=
  if j = 0 then [] else if j = 1 then [[(true, tc)]]
  else if j % 2 = 0 then [[(true, 20 * Nat.pair tc (j / 2) + 18)], [(true, 20 * Nat.pair tc (j / 2) + 18)]]
  else [[(true, tc)], [(true, 20 * Nat.pair tc (j - 1) + 18)]]

theorem seqBody_num (t : TMTask (QH k) GH) (j : ℕ) :
    (seqBody t j).map (·.map labH) = seqN (encTMTask gN t) j := by
  unfold seqBody seqN; split_ifs <;> rfl

theorem parBody_num (t : TMTask (QH k) GH) (j : ℕ) :
    (parBody t j).map (·.map labH) = parN (encTMTask gN t) j := by
  unfold parBody parN; split_ifs <;> rfl

/-- The checker body, numbered. -/
def checkersN (K i : ℕ) : List (List (Bool × ℕ)) :=
  if i = 0 then [] else if i = 1 then [[(true, 21), (true, 20 * Nat.pair 12 K + 17), (true, 41)]]
  else if i % 2 = 0 then
    [[(true, 20 * Nat.pair (20 * (i / 2) + 6) (i / 2) + 18), (true, 20 * (i / 2) + 13)],
      [(true, 20 * (i / 2) + 13), (true, 20 * Nat.pair (20 * (i / 2) + 6) (i / 2) + 18)]]
  else [[(true, 20 * Nat.pair 26 (i - 1) + 18), (true, 20 * (i - 1) + 13)],
      [(true, 33), (true, 20 * (i - 1) + 6)]]

theorem checkersBody_num (K i : ℕ) :
    (checkersBody (Q := QH k) (Γ := GH) K i).map (·.map labH) = checkersN K i := by
  unfold checkersBody checkersN; split_ifs <;> rfl

theorem foldl_pred (f : ℕ) : ∀ l : List Unit, l.foldl (fun s _ => s - 1) f = f - l.length := by
  intro l
  induction l generalizing f with
  | nil => rfl
  | cons u l ih => rw [List.foldl_cons, ih]; simp; omega

theorem pt_subLength {α : Type} [BEnc α] {f : α → ℕ} {l : α → List Unit} (hf : PT f) (hl : PT l) :
    PT fun a => f a - (l a).length :=
  (PT.foldl (g := fun _ s _ => s - 1) hl hf (PT.pred (PT.fst.comp PT.snd)) (c := 0) (d := 0)
    fun a s b _ => by simpa using sz_sub_le s 1).of_eq fun a => foldl_pred _ _

end Numeric

/-! ### The word -/

section Word

variable (N : NTM (Fin k) Space.TapeSym)

/-- The letter of the normalised input at a position. -/
def letterH (x : List Bool) (i : ℕ) : GH :=
  if i < x.length then (some (x.getI i), decide (i = 0)) else (N.blank, false)

theorem markInput_getD' (x : List Bool) (i : ℕ) :
    (markInput N (x.map some)).getD i (homingMachine N).blank = letterH N x i := by
  unfold markInput letterH
  by_cases h : i < x.length
  · rw [if_pos h, List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [List.getI_eq_getElem _ h]
  · rw [if_neg h, List.getD_eq_default _ _ (by simp; omega)]
    rfl

/-- The word body, numbered. -/
def wordN (x : List Bool) (i : ℕ) : List (List (Bool × ℕ)) :=
  if i + 1 < x.length then
    [[(true, 20 * (gN (letterH N x i) + 1) + 3), (true, 20 * (i + 1) + 15)]]
  else [[(true, 20 * (gN (letterH N x i) + 1) + 3)]]

theorem wordBody_num (x : List Bool) (i : ℕ) :
    (wordBody (homingMachine N) (markInput N (x.map some)) i).map (·.map labH) = wordN N x i := by
  unfold wordBody wordN
  rw [markInput_getD', markInput_length, List.length_map]
  split_ifs <;> rfl

variable {α : Type} [BEnc α]

theorem pt_letterH {x : α → List Bool} {i : α → ℕ} (hx : PT x) (hi : PT i) :
    PT fun a => letterH N (x a) (i a) := by
  unfold letterH
  exact PT.ite (PT.lt hi (PT.length hx)) (PT.pair (PT.some (PT.getI hx hi)) (PT.eq hi (PT.const 0)))
    (PT.const _)

theorem pt_wordN {x : α → List Bool} {i : α → ℕ} (hx : PT x) (hi : PT i) :
    PT fun a => wordN N (x a) (i a) := by
  have hl := (pt_of_finite gN).comp (pt_letterH N hx hi)
  unfold wordN
  exact PT.ite (PT.lt (PT.succ hi) (PT.length hx))
    (PT.single (PT.cons (PT.pair (PT.const true) (PT.affine 20 3 (PT.succ hl)))
      (PT.single (PT.pair (PT.const true) (PT.affine 20 15 (PT.succ hi))))))
    (PT.single (PT.single (PT.pair (PT.const true) (PT.affine 20 3 (PT.succ hl)))))

end Word

section PTN

variable {α : Type} [BEnc α]

theorem pt_seqN (tc : ℕ) {j : α → ℕ} (hj : PT j) : PT fun a => seqN tc (j a) := by
  unfold seqN
  have h1 := PT.affine 20 17 (PT.natPair (PT.const tc) (PT.divC hj (c := 2) (by norm_num)))
  have h2 := PT.affine 20 17 (PT.natPair (PT.const tc) (PT.pred hj))
  exact PT.ite (PT.eq hj (PT.const 0)) (PT.const _) (PT.ite (PT.eq hj (PT.const 1)) (PT.const _)
    (PT.ite (PT.eq (PT.modC hj (c := 2) (by norm_num)) (PT.const 0))
      (PT.single (PT.cons (PT.pair (PT.const true) h1) (PT.single (PT.pair (PT.const true) h1))))
      (PT.single (PT.cons (PT.const _) (PT.single (PT.pair (PT.const true) h2))))))

theorem pt_seqNv {tc j : α → ℕ} (htc : PT tc) (hj : PT j) : PT fun a => seqN (tc a) (j a) := by
  unfold seqN
  have h1 := PT.affine 20 17 (PT.natPair htc (PT.divC hj (c := 2) (by norm_num)))
  have h2 := PT.affine 20 17 (PT.natPair htc (PT.pred hj))
  exact PT.ite (PT.eq hj (PT.const 0)) (PT.const _) (PT.ite (PT.eq hj (PT.const 1))
    (PT.single (PT.single (PT.pair (PT.const true) htc)))
    (PT.ite (PT.eq (PT.modC hj (c := 2) (by norm_num)) (PT.const 0))
      (PT.single (PT.cons (PT.pair (PT.const true) h1) (PT.single (PT.pair (PT.const true) h1))))
      (PT.single (PT.cons (PT.pair (PT.const true) htc) (PT.single (PT.pair (PT.const true) h2))))))

theorem pt_parN {tc j : α → ℕ} (htc : PT tc) (hj : PT j) : PT fun a => parN (tc a) (j a) := by
  unfold parN
  have h1 := PT.affine 20 18 (PT.natPair htc (PT.divC hj (c := 2) (by norm_num)))
  have h2 := PT.affine 20 18 (PT.natPair htc (PT.pred hj))
  exact PT.ite (PT.eq hj (PT.const 0)) (PT.const _) (PT.ite (PT.eq hj (PT.const 1))
    (PT.single (PT.single (PT.pair (PT.const true) htc)))
    (PT.ite (PT.eq (PT.modC hj (c := 2) (by norm_num)) (PT.const 0))
      (PT.cons (PT.single (PT.pair (PT.const true) h1)) (PT.single (PT.single (PT.pair (PT.const true) h1))))
      (PT.cons (PT.single (PT.pair (PT.const true) htc))
        (PT.single (PT.single (PT.pair (PT.const true) h2))))))

theorem pt_checkersN {K i : α → ℕ} (hK : PT K) (hi : PT i) : PT fun a => checkersN (K a) (i a) := by
  unfold checkersN
  have hh := PT.divC hi (c := 2) (by norm_num)
  have hp := PT.pred hi
  have e1 := PT.affine 20 18 (PT.natPair (PT.affine 20 6 hh) hh)
  have e2 := PT.affine 20 13 hh
  exact PT.ite (PT.eq hi (PT.const 0)) (PT.const _) (PT.ite (PT.eq hi (PT.const 1))
    (PT.single (PT.cons (PT.const _) (PT.cons (PT.pair (PT.const true)
      (PT.affine 20 17 (PT.natPair (PT.const 12) hK))) (PT.const _))))
    (PT.ite (PT.eq (PT.modC hi (c := 2) (by norm_num)) (PT.const 0))
      (PT.cons (PT.cons (PT.pair (PT.const true) e1) (PT.single (PT.pair (PT.const true) e2)))
        (PT.single (PT.cons (PT.pair (PT.const true) e2) (PT.single (PT.pair (PT.const true) e1)))))
      (PT.cons (PT.cons (PT.pair (PT.const true) (PT.affine 20 18 (PT.natPair (PT.const 26) hp)))
        (PT.single (PT.pair (PT.const true) (PT.affine 20 13 hp))))
        (PT.single (PT.cons (PT.const _) (PT.single (PT.pair (PT.const true)
          (PT.affine 20 6 hp))))))))

theorem pt_countsL {K n : α → ℕ} (hK : PT K) (hn : PT n) (hsub : PT fun a => K a - n a) :
    PT fun a => countsL (K a) (n a) := by
  unfold countsL
  exact PT.append (PT.append (PT.append (PT.append (PT.append (pt_hcL hK) (pt_hcL (PT.succ hK)))
    (pt_hcL (PT.succ (PT.succ hK)))) (pt_hcL hsub)) (pt_hcL (PT.pred hK)))
    (PT.cons (PT.const 0) (PT.cons (PT.const 1) (PT.single hK)))

end PTN

/-! ### The numbered methods -/

section Methods

variable (N : NTM (Fin k) Space.TapeSym)

/-- **The numbered methods**, for the word `x` and the time bound `K`. -/
noncomputable def methodsNum (x : List Bool) (K : ℕ) : List (ℕ × List (List (Bool × ℕ))) :=
  (syncAll.map fun y => encB (k := k) (.acquire y, [[Sum.inl (.call y), Sum.inl (.wait y)]])) ++
  (syncAll.map fun y => encB (k := k) (.release y, [[Sum.inl (.start y), Sum.inl (.respond y)]])) ++
  symList.map (fun c => (2, [[labH (k := k) (Sum.inl (.assert c)), (true, 0),
    (true, 20 * Nat.pair 20 (K + 1) + 17), (true, 20 * Nat.pair 40 (K + 1) + 17)]])) ++
  symList.map (fun c => (20 * encSym gN c + 3, [[labH (k := k) (Sum.inl (.assert c)), (true, 0),
    (true, 20 * Nat.pair 20 (K + 1) + 17), (true, 20 * Nat.pair 40 (K + 1) + 17)]])) ++
  [(4, [[(true, 3), (true, 20 * Nat.pair 2 K + 17)]]),
    encB (k := k) (.waitCell, [[Sum.inr (.release .check), Sum.inr (.release .sync)]])] ++
  (countsL K x.length).map (fun i => (20 * i + 6, [[(true, 20 * Nat.pair 5 i + 17)]])) ++
  symList.map (fun c => (7, [[labH (k := k) (Sum.inl (.check (.sym c))), (true, 41),
    (true, 20 * K + 6), (true, 21), labH (k := k) (Sum.inl (.check (.sym c)))]])) ++
  [encB (k := k) (.headCell, [[Sum.inl (.start .head), Sum.inl .assertHead, Sum.inl (.respond .head)]]),
    encB (k := k) (.noHeadCell, [[Sum.inl (.start .head), Sum.inl .retractHead,
      Sum.inl (.respond .head)]]),
    (10, [[(true, 9), (true, 8), (true, 20 * Nat.pair 9 K + 17)]])] ++
  (transAll (homingMachine N)).map (fun t => encB (.transition, transBody t)) ++
  [encB (k := k) (.transitionAndCheck, [[Sum.inr .transition, Sum.inr .chk]]),
    encB (k := k) (.transitionAndCheck, [[Sum.inl (.check .noHead), Sum.inr .chk]])] ++
  (countsL K x.length).map (fun i => (20 * i + 13, checkersN K i)) ++
  [(14, [[(true, 3), (true, 15), (true, 20 * Nat.pair (20 * (gN (N.blank, false) + 1) + 3)
    (K - x.length) + 17)]])] ++
  (List.range (x.length + 1)).map (fun i => (20 * i + 15, wordN N x i)) ++
  (accAll (homingMachine N)).map (fun f => encB (.done, [[Sum.inl (.check (.st f))]])) ++
  (((baseAll (homingMachine N)).map (encTMTask gN)).flatMap fun tc =>
    (countsL K x.length).map fun j => (20 * Nat.pair tc j + 17, seqN tc j)) ++
  ((countsL K x.length).flatMap fun i => (countsL K x.length).map fun j =>
    (20 * Nat.pair (20 * i + 6) j + 18, parN (20 * i + 6) j))

set_option maxHeartbeats 1000000 in
theorem methodsL_num (x : List Bool) (K : ℕ) :
    (methodsL (homingMachine N) (markInput N (x.map some)) K).map encB = methodsNum N x K := by
  unfold methodsL methodsNum
  simp only [List.map_append, markInput_length, List.length_map]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_)
    ?_) ?_) ?_) ?_) ?_) ?_) ?_
  all_goals first
    | rfl
    | (simp only [List.map_map, Function.comp_def]; rfl)
    | (simp only [List.map_map, Function.comp_def, encB, checkersBody_num] <;> rfl)
    | (simp only [List.map_map, Function.comp_def, encB, wordBody_num] <;> rfl)
    | (simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, encB,
        seqBody_num] <;> rfl)
    | (simp only [List.map_flatMap, List.map_map, Function.comp_def, encB, parBody_num] <;> rfl)

end Methods

section PTMethods

variable (N : NTM (Fin k) Space.TapeSym) {α : Type} [BEnc α]

/-- **The numbered methods are computed in polynomial time.** -/
theorem pt_methodsNum {x : α → List Bool} {K : α → ℕ} (hx : PT x) (hK : PT K) :
    PT fun a => methodsNum N (x a) (K a) := by
  have hu : PT fun a => (x a).map fun _ => () := PT.map (g := fun _ _ => ()) hx (PT.const ())
  have hsub : PT fun a => K a - (x a).length :=
    (pt_subLength hK hu).of_eq fun a => by simp
  have hC : PT fun a => countsL (K a) (x a).length := pt_countsL hK (PT.length hx) hsub
  have hK1 : PT fun q : α × Option GH => K q.1 := hK.comp PT.fst
  have hKc : PT fun a => (true, 20 * Nat.pair 20 (K a + 1) + 17) :=
    PT.pair (PT.const true) (PT.affine 20 17 (PT.natPair (PT.const 20) (PT.succ hK)))
  have hKs : PT fun a => (true, 20 * Nat.pair 40 (K a + 1) + 17) :=
    PT.pair (PT.const true) (PT.affine 20 17 (PT.natPair (PT.const 40) (PT.succ hK)))
  unfold methodsNum
  refine PT.append (PT.append (PT.append (PT.append (PT.append (PT.append (PT.append (PT.append
    (PT.append (PT.append (PT.append (PT.append (PT.append (PT.append (PT.append
      (PT.const _) (PT.const _)) ?_) ?_) ?_) ?_) ?_) ?_) (PT.const _)) (PT.const _)) ?_) ?_) ?_)
      (PT.const _)) ?_) ?_
  · exact PT.map (PT.const symList) (PT.pair (PT.const 2) (PT.single (PT.cons
      (pt_lab_inl TMAct.assert PT.snd) (PT.cons (PT.const _) (PT.cons (hKc.comp PT.fst)
        (PT.single (hKs.comp PT.fst)))))))
  · exact PT.map (PT.const symList) (PT.pair ((pt_of_finite fun c : Option GH =>
      20 * encSym gN c + 3).comp PT.snd) (PT.single (PT.cons
      (pt_lab_inl TMAct.assert PT.snd) (PT.cons (PT.const _) (PT.cons (hKc.comp PT.fst)
        (PT.single (hKs.comp PT.fst)))))))
  · exact PT.cons (PT.pair (PT.const _) (PT.single (PT.cons (PT.const _) (PT.single (PT.pair
      (PT.const true) (PT.affine 20 17 (PT.natPair (PT.const 2) hK))))))) (PT.const _)
  · exact PT.map hC (PT.pair (PT.affine 20 6 PT.snd) (PT.single (PT.single (PT.pair (PT.const true)
      (PT.affine 20 17 (PT.natPair (PT.const 5) PT.snd))))))
  · exact PT.map (PT.const symList) (PT.pair (PT.const 7) (PT.single (PT.cons
      (pt_lab_inl (fun c => TMAct.check (TMFact.sym c)) PT.snd) (PT.cons (PT.const _)
        (PT.cons (PT.pair (PT.const true) (PT.affine 20 6 hK1)) (PT.cons (PT.const _)
          (PT.single (pt_lab_inl (fun c => TMAct.check (TMFact.sym c)) PT.snd))))))))
  · exact PT.cons (PT.const _) (PT.cons (PT.const _) (PT.single (PT.pair (PT.const _)
      (PT.single (PT.cons (PT.const _) (PT.cons (PT.const _) (PT.single (PT.pair (PT.const true)
        (PT.affine 20 17 (PT.natPair (PT.const 9) hK))))))))))
  · exact PT.map hC (PT.pair (PT.affine 20 13 PT.snd) (pt_checkersN (hK.comp PT.fst) PT.snd))
  · exact PT.single (PT.pair (PT.const _) (PT.single (PT.cons (PT.const _) (PT.cons (PT.const _)
      (PT.single (PT.pair (PT.const true) (PT.affine 20 17 (PT.natPair (PT.const _) hsub))))))))
  · exact PT.map ((PT.rangeLength (PT.append hx (PT.const [false]))).of_eq fun a => by simp)
      (PT.pair (PT.affine 20 15 PT.snd) (pt_wordN N (hx.comp PT.fst) PT.snd))
  · exact PT.flatMap (PT.const _) (PT.map (hC.comp PT.fst) (PT.pair (PT.affine 20 17
      (PT.natPair (PT.snd.comp PT.fst) PT.snd)) (pt_seqNv (PT.snd.comp PT.fst) PT.snd)))
  · exact PT.flatMap hC (PT.map (hC.comp PT.fst) (PT.pair (PT.affine 20 18
      (PT.natPair (PT.affine 20 6 (PT.snd.comp PT.fst)) PT.snd))
      (pt_parN (PT.affine 20 6 (PT.snd.comp PT.fst)) PT.snd)))

end PTMethods

end U

end TMEnc

end HTN
