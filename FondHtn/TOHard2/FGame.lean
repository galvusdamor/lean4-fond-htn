import FondHtn.TOHard2.Auto
/-!
# The fair list game of a grammar

The fair (strong cyclic, Cimatti et al.) counterpart of the list game `FOND.TOHard2.LGH`.  A
*fair set* `Y` (with target `Ψ`) is a set of positions (list of symbols, configuration) each of
which lies in the **attractor** `FOND.TOHard2.FA G Ψ Y`: the empty list in a target
configuration; an instruction with an applicable alternative all of whose outcomes stay in `Y`
and *one* of which is in the attractor of lower rank; a nonterminal with a body whose position
stays in `Y` and is in the attractor of lower rank.

The calculus: unfolding of instructions and nonterminals (`y_ins`, `y_comp`, `fa_ins`,
`fa_comp`), programs (`y_prog`), sequential splitting (`fa_split`, `fset_split`) and the left
recursion (`fa_lam`, `y_lam`).  In contrast to the strong game, nothing bounds the plays; the
rank only bounds the distance to the target along one path.
-/

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

variable (G : Gram) (Ψ : Set Cfg) (Y : List (Bool × ℕ) → Cfg → Prop)

/-- **The attractor** of the target `Ψ` with respect to the fair set `Y`, graded by rank. -/
inductive FA : ℕ → List (Bool × ℕ) → Cfg → Prop
  | nil {n : ℕ} {c : Cfg} (h : c ∈ Ψ) : FA n [] c
  | ins {n m : ℕ} {I : List ASpec} {a : ASpec} {xs : List (Bool × ℕ)} {c c₀ : Cfg}
      (hI : (m, I) ∈ G.insL) (ha : a ∈ I) (happ : a.App c) (hall : ∀ c' ∈ a.Out c, Y xs c')
      (hc₀ : c₀ ∈ a.Out c) (h : FA n xs c₀) : FA (n + 1) ((false, m) :: xs) c
  | comp {n m : ℕ} {bs xs : List (Bool × ℕ)} {c : Cfg} (hb : (m, bs) ∈ G.methL)
      (hY : Y (bs ++ xs) c) (h : FA n (bs ++ xs) c) : FA (n + 1) ((true, m) :: xs) c

/-- **A fair set**: every position is in the attractor. -/
def FSet : Prop := ∀ xs c, Y xs c → ∃ n, FA G Ψ Y n xs c

variable {G Ψ Y}

theorem FA.mono {n : ℕ} {xs : List (Bool × ℕ)} {c : Cfg} (h : FA G Ψ Y n xs c) :
    ∀ {n'}, n ≤ n' → FA G Ψ Y n' xs c := by
  induction h with
  | nil h => exact fun _ => .nil h
  | ins hI ha happ hall hc₀ _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .ins hI ha happ hall hc₀ (ih (by omega))
  | comp hb hY _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .comp hb hY (ih (by omega))

theorem FA.monoΨ {n : ℕ} {xs : List (Bool × ℕ)} {c : Cfg} (h : FA G Ψ Y n xs c) {Ψ' : Set Cfg}
    (hΨ : Ψ ⊆ Ψ') : FA G Ψ' Y n xs c := by
  induction h with
  | nil h => exact .nil (hΨ h)
  | ins hI ha happ hall hc₀ _ ih => exact .ins hI ha happ hall hc₀ ih
  | comp hb hY _ ih => exact .comp hb hY ih

theorem FSet.monoΨ (h : FSet G Ψ Y) {Ψ' : Set Cfg} (hΨ : Ψ ⊆ Ψ') : FSet G Ψ' Y :=
  fun xs c hY => let ⟨n, hn⟩ := h xs c hY; ⟨n, hn.monoΨ hΨ⟩

theorem not_fa_zero {y : Bool × ℕ} {xs : List (Bool × ℕ)} {c : Cfg} : ¬ FA G Ψ Y 0 (y :: xs) c :=
  fun h => by cases h

theorem fa_nil {n : ℕ} {c : Cfg} (h : FA G Ψ Y n [] c) : c ∈ Ψ := by
  cases h with | nil h => exact h

theorem y_nil (hY : FSet G Ψ Y) {c : Cfg} (h : Y [] c) : c ∈ Ψ :=
  let ⟨_, hn⟩ := hY _ _ h; fa_nil hn

theorem fa_ins (hnd : G.InsNodup) {n m : ℕ} {I : List ASpec} (hI : (m, I) ∈ G.insL)
    {xs : List (Bool × ℕ)} {c : Cfg} (h : FA G Ψ Y (n + 1) ((false, m) :: xs) c) :
    ∃ a ∈ I, a.App c ∧ (∀ c' ∈ a.Out c, Y xs c') ∧ ∃ c₀ ∈ a.Out c, FA G Ψ Y n xs c₀ := by
  cases h with
  | ins hI' ha happ hall hc₀ h =>
    rw [hnd.uniq hI' hI] at ha
    exact ⟨_, ha, happ, hall, _, hc₀, h⟩

theorem fa_comp {n m : ℕ} {xs : List (Bool × ℕ)} {c : Cfg}
    (h : FA G Ψ Y (n + 1) ((true, m) :: xs) c) :
    ∃ bs, (m, bs) ∈ G.methL ∧ Y (bs ++ xs) c ∧ FA G Ψ Y n (bs ++ xs) c := by
  cases h with | comp hb hY h => exact ⟨_, hb, hY, h⟩

theorem y_ins (hY : FSet G Ψ Y) (hnd : G.InsNodup) {m : ℕ} {I : List ASpec} (hI : (m, I) ∈ G.insL)
    {xs : List (Bool × ℕ)} {c : Cfg} (h : Y ((false, m) :: xs) c) :
    c ∈ wpI I {c' | Y xs c'} := by
  obtain ⟨n, hn⟩ := hY _ _ h
  rcases n with _ | n
  · exact absurd hn not_fa_zero
  obtain ⟨a, ha, happ, hall, -⟩ := fa_ins hnd hI hn
  exact ⟨a, ha, happ, hall⟩

theorem y_comp (hY : FSet G Ψ Y) {m : ℕ} {xs : List (Bool × ℕ)} {c : Cfg}
    (h : Y ((true, m) :: xs) c) : ∃ bs, (m, bs) ∈ G.methL ∧ Y (bs ++ xs) c := by
  obtain ⟨n, hn⟩ := hY _ _ h
  rcases n with _ | n
  · exact absurd hn not_fa_zero
  obtain ⟨bs, hb, hY', -⟩ := fa_comp hn
  exact ⟨bs, hb, hY'⟩

/-- **A program of instructions**, in a fair set. -/
theorem y_prog (hY : FSet G Ψ Y) (hnd : G.InsNodup) {prog : List (ℕ × List ASpec)}
    (hp : ∀ p ∈ prog, p ∈ G.insL) :
    ∀ {xs : List (Bool × ℕ)} {c : Cfg}, Y (syms prog ++ xs) c → c ∈ wpP (inss prog) {c' | Y xs c'} := by
  induction prog with
  | nil => intro xs c h; exact h
  | cons p prog ih =>
    intro xs c h
    rw [syms_cons, List.cons_append] at h
    have h' := y_ins hY hnd (hp p (by simp)) h
    rw [inss_cons, wpP_cons]
    exact wpI_mono (fun c' hc' => ih (fun q hq => hp q (by simp [hq])) hc') h'

/-! ## Sequential splitting -/

/-- **Splitting the attractor**: a position `xs ++ ys` of the fair set reaches the target only
through the positions `ys`. -/
theorem fa_split {ys : List (Bool × ℕ)} {n : ℕ} {l : List (Bool × ℕ)} {c : Cfg}
    (h : FA G Ψ Y n l c) : ∀ {xs : List (Bool × ℕ)}, l = xs ++ ys → Y l c →
      FA G {c' | Y ys c'} (fun u c' => Y (u ++ ys) c') n xs c := by
  induction h with
  | @nil n c hc =>
    intro xs he hYl
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 he.symm
    exact .nil hYl
  | @ins n m I a l c c₀ hI ha happ hall hc₀ _ ih =>
    intro xs he hYl
    rcases xs with _ | ⟨z, xs⟩
    · rw [List.nil_append] at he; subst he; exact .nil hYl
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .ins hI ha happ hall hc₀ (ih rfl (hall c₀ hc₀))
  | @comp n m bs l c hb hYb _ ih =>
    intro xs he hYl
    rcases xs with _ | ⟨z, xs⟩
    · rw [List.nil_append] at he; subst he; exact .nil hYl
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine .comp hb (by simpa [List.append_assoc] using hYb) (ih (by simp [List.append_assoc]) hYb)

theorem fset_split (hY : FSet G Ψ Y) (ys : List (Bool × ℕ)) :
    FSet G {c' | Y ys c'} (fun u c' => Y (u ++ ys) c') :=
  fun xs c h => let ⟨n, hn⟩ := hY _ _ h; ⟨n, fa_split hn rfl h⟩

/-! ## The left recursion -/

section Lam

variable {A : Aut} {lam : ℕ → ℕ} {y : ℕ} {blk : AT → List (ℕ × List ASpec)}

/-- **The left recursion**: the policy commits a run before the body executes (the rank bounds
the number of unfoldings). -/
theorem fa_lam (hΛ : ∀ σ bs, (lam σ, bs) ∈ G.methL → ∃ σ' a, (σ', a, σ) ∈ A.trans ∧
      (bs = (true, lam σ') :: syms (blk a) ∨ (σ' = A.init ∧ bs = (true, y) :: syms (blk a)))) :
    ∀ {n : ℕ} {σ : ℕ} {xs : List (Bool × ℕ)} {c : Cfg},
    FA G Ψ Y n ((true, lam σ) :: xs) c →
      ∃ as, Run A as σ ∧ Y ((true, y) :: syms (as.flatMap blk) ++ xs) c ∧
        FA G Ψ Y n ((true, y) :: syms (as.flatMap blk) ++ xs) c := by
  intro n
  induction n with
  | zero => intro σ xs c h; exact absurd h not_fa_zero
  | succ n ih =>
    intro σ xs c h
    obtain ⟨bs, hb, hYb, h⟩ := fa_comp h
    obtain ⟨σ', a, ht, rfl | ⟨rfl, rfl⟩⟩ := hΛ σ bs hb
    · rw [List.cons_append] at h hYb
      obtain ⟨as, hrun, hY', h'⟩ := ih h
      refine ⟨as ++ [a], .snoc hrun ht, ?_, ?_⟩
      · simpa [List.flatMap_append, List.append_assoc] using hY'
      · have := h'.mono (n' := n + 1) (by omega)
        simpa [List.flatMap_append, List.append_assoc] using this
    · refine ⟨[a], .one ht, by simpa using hYb, ?_⟩
      have := h.mono (n' := n + 1) (by omega)
      simpa using this

theorem y_lam (hY : FSet G Ψ Y)
    (hΛ : ∀ σ bs, (lam σ, bs) ∈ G.methL → ∃ σ' a, (σ', a, σ) ∈ A.trans ∧
      (bs = (true, lam σ') :: syms (blk a) ∨ (σ' = A.init ∧ bs = (true, y) :: syms (blk a))))
    {σ : ℕ} {xs : List (Bool × ℕ)} {c : Cfg} (h : Y ((true, lam σ) :: xs) c) :
    ∃ as, Run A as σ ∧ Y ((true, y) :: syms (as.flatMap blk) ++ xs) c := by
  obtain ⟨n, hn⟩ := hY _ _ h
  obtain ⟨as, hrun, hY', -⟩ := fa_lam hΛ hn
  exact ⟨as, hrun, hY'⟩

end Lam

end TOHard2

end FOND
