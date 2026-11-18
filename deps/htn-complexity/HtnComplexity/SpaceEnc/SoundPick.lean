import HtnComplexity.SpaceEnc.SoundLemmas
/-!
# Soundness of the encoding: which word does a step advance?

A step of the plan advances one word of the world.  These lemmas locate it:

* `HTN.SpaceEnc.fresh_par` — a word of a fresh block of parity `q` can only fire when the parity
  fact is `q`;
* `HTN.SpaceEnc.pickW`, `pickR`, `pickF`, `pickAllFresh` — the block a step takes its word from;
* `HTN.SpaceEnc.writer_word` — the kinds of words of the writer's current block that can fire;
* `HTN.SpaceEnc.blocks_set` — the blocks after the step.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] {m n' : ℕ} {ι : Bool → Γ} {N : NTM Q Γ}
  {w : List Bool} {fs : FS Q Γ}

/-- **A word of a fresh block of parity `q` only fires when the parity is `q`.** -/
theorem fresh_par {q : Bool} {bl : List (List (Act Q Γ))} (hF : FreshBlock m n' N q bl)
    {a : Act Q Γ} {t : List (Act Q Γ)} (hv : a :: t ∈ bl)
    (happ : (am m n' ι N).Applicable a (enc m w fs)) : fs.par = q := by
  rcases hF.mem hv with ⟨cd, -, hcd⟩ | ⟨b, hb, hb'⟩
  · rw [chainW_eq] at hcd
    obtain ⟨rfl, -⟩ := List.cons.inj hcd
    exact ((app_ws m n' ι N w fs).1 happ).2
  · obtain ⟨rfl, -⟩ := List.cons.inj hb'
    exact par_of_app_h hb happ

/-- **The block of a step among blocks with a non-empty current block.** -/
theorem pickW {q : Bool} {bsq E rest : List (List (List (Act Q Γ)))}
    {P : List (List (Act Q Γ)) → Prop} {bl : List (List (Act Q Γ))} {i : ℕ} {v : List (Act Q Γ)}
    (hB : Blocks m n' N q bsq P) (hne : ∀ cur, P cur → ¬ AllEmpty cur)
    (hbq : bsq = E ++ bl :: rest) (hE : AllE E) (hi : bl[i]? = some v) (hv : v ≠ []) :
    P bl ∧ ∀ b ∈ rest, FreshBlock m n' N q b := by
  obtain ⟨E', cur, F, h1, hE', hP, hF⟩ := hB
  rcases locate h1 hE' hF hbq hE (not_allEmpty_of_get hi hv) with ⟨rfl, rfl⟩ | ⟨hA, -⟩
  · exact ⟨hP, hF⟩
  · exact absurd hA (hne cur hP)

/-- **The block of a step of the reader**: the reader's fresh blocks cannot fire (wrong
parity), so the step advances a word of its current block. -/
theorem pickR {q : Bool} {bsq E rest : List (List (List (Act Q Γ)))}
    {P : List (List (Act Q Γ)) → Prop} {bl : List (List (Act Q Γ))} {i : ℕ} {a : Act Q Γ}
    {t : List (Act Q Γ)} (hB : Blocks m n' N q bsq P)
    (hbq : bsq = E ++ bl :: rest) (hE : AllE E) (hi : bl[i]? = some (a :: t))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) (hpar : fs.par ≠ q) :
    P bl ∧ ∀ b ∈ rest, FreshBlock m n' N q b := by
  obtain ⟨E', cur, F, h1, hE', hP, hF⟩ := hB
  rcases locate h1 hE' hF hbq hE (not_allEmpty_of_get hi (List.cons_ne_nil _ _)) with
    ⟨rfl, rfl⟩ | ⟨-, hF'⟩
  · exact ⟨hP, hF⟩
  · exact absurd (fresh_par (hF bl (by rw [hF']; simp)) (List.mem_of_getElem? hi) happ) hpar

/-- **The block of a step among blocks that are consumed or fresh.** -/
theorem pickF {q : Bool} {bsq E rest : List (List (List (Act Q Γ)))}
    {bl : List (List (Act Q Γ))} {i : ℕ} {v : List (Act Q Γ)}
    (hB : BlocksF m n' N q bsq) (hbq : bsq = E ++ bl :: rest) (hE : AllE E)
    (hi : bl[i]? = some v) (hv : v ≠ []) :
    FreshBlock m n' N q bl ∧ ∀ b ∈ rest, FreshBlock m n' N q b := by
  obtain ⟨E', F, h1, hE', hF⟩ := hB
  have h := locateF h1 hE' hF hbq hE (not_allEmpty_of_get hi hv)
  subst h
  exact ⟨hF bl (by simp), fun b hb => hF b (by simp [hb])⟩

/-- **Fresh blocks of the wrong parity cannot fire.** -/
theorem pickAllFresh {q : Bool} {bsq E rest : List (List (List (Act Q Γ)))}
    {bl : List (List (Act Q Γ))} {i : ℕ} {a : Act Q Γ} {t : List (Act Q Γ)}
    (hF : ∀ b ∈ bsq, FreshBlock m n' N q b)
    (hbq : bsq = E ++ bl :: rest) (hi : bl[i]? = some (a :: t))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) (hpar : fs.par ≠ q) : False :=
  hpar (fresh_par (hF bl (by rw [hbq]; simp)) (List.mem_of_getElem? hi) happ)

/-- The blocks after a step. -/
theorem blocks_set {q : Bool} {rest : List (List (List (Act Q Γ)))}
    {P : List (List (Act Q Γ)) → Prop} {cur : List (List (Act Q Γ))} (hP : P cur)
    (hrest : ∀ b ∈ rest, FreshBlock m n' N q b) : Blocks m n' N q (cur :: rest) P :=
  ⟨[], cur, rest, rfl, by simp [AllE], hP, hrest⟩

omit [Fintype Q] [Fintype Γ] in
/-- The membership in the writer's current block. -/
theorem mem_wcur {p : Bool} {c : ℕ} {nv : ℕ → Γ} {X : Multiset (List (Act Q Γ))}
    {Fr : Multiset (CD Q Γ)} {h : Act Q Γ} {v : List (Act Q Γ)}
    (hv : v ∈ Fr.map (chainW m p) + {[h]} + tails m p nv (List.range c) + X) :
    (∃ cd ∈ Fr, v = chainW m p cd) ∨ v = [h] ∨ (∃ c' < c, v = tl m p c' (nv c')) ∨ v ∈ X := by
  simp only [Multiset.mem_add, Multiset.mem_map, Multiset.mem_singleton] at hv
  rcases hv with ((⟨cd, hcd, rfl⟩ | rfl) | ht) | hX
  · exact Or.inl ⟨cd, hcd, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · obtain ⟨c', hc', rfl⟩ := mem_tails ht
    exact Or.inr (Or.inr (Or.inl ⟨c', List.mem_range.1 hc', rfl⟩))
  · exact Or.inr (Or.inr (Or.inr hX))

omit [Fintype Q] in
/-- **The words of the writer's current block that can fire**: an unstarted chain word (program
counter `0`), the head move word (program counter `2m + 4`) or a word in progress; the stored
tails of the writer cannot fire during its own round. -/
theorem writer_word {p : Bool} {c : ℕ} {nv : ℕ → Γ} {X : Multiset (List (Act Q Γ))}
    {Fr : Multiset (CD Q Γ)} {h : Act Q Γ} (hh : IsHActP p h) {a : Act Q Γ} {t : List (Act Q Γ)}
    (hv : a :: t ∈ Fr.map (chainW m p) + {[h]} + tails m p nv (List.range c) + X)
    (happ : (am m n' ι N).Applicable a (enc m w fs)) (hpar : fs.par = p) :
    (fs.pc = 0 ∧ a = .ws p ∧ ∃ cd ∈ Fr, a :: t = chainW m p cd) ∨
      (fs.pc = 2 * m + 4 ∧ a = h ∧ t = []) ∨ a :: t ∈ X := by
  rcases mem_wcur hv with ⟨cd, hcd, he⟩ | he | ⟨c', -, he⟩ | hX
  · have he' := he
    rw [chainW_eq] at he'
    obtain ⟨rfl, -⟩ := List.cons.inj he'
    exact Or.inl ⟨((app_ws m n' ι N w fs).1 happ).1, rfl, cd, hcd, he⟩
  · obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact Or.inr (Or.inl ⟨(pc_of_app happ).trans (pcNeed_h hh), rfl, rfl⟩)
  · rw [tl_eq] at he
    obtain ⟨rfl, -⟩ := List.cons.inj he
    have := ((app_rv m n' ι N w fs).1 happ).2
    rw [hpar] at this
    cases p <;> simp at this
  · exact Or.inr (Or.inr hX)

theorem update_self' {α : Type*} (bs : Bool → α) (q : Bool) (x : α) :
    Function.update bs q x q = x := Function.update_self q x bs

theorem update_not {α : Type*} (bs : Bool → α) (q : Bool) (x : α) :
    Function.update bs q x (!q) = bs (!q) :=
  Function.update_of_ne (by cases q <;> simp) x bs

theorem bool_eq_not_of_ne {q p : Bool} (h : q ≠ p) : q = !p := by
  cases q <;> cases p <;> simp_all

end SpaceEnc

end HTN

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] {m n' : ℕ} {ι : Bool → Γ} {N : NTM Q Γ}
  {w : List Bool} {fs : FS Q Γ}

/-- **A step of the reader at position `c`** reads one of its stored tails (program counter
`m + 1`); in round `0` the reader cannot fire at all. -/
theorem reader_fire {p : Bool} {cfg : Config Q Γ} {first : Bool} {c : ℕ}
    {bsR E rest : List (List (List (Act Q Γ)))} {bl : List (List (Act Q Γ))} {i : ℕ}
    {a : Act Q Γ} {t : List (Act Q Γ)} (hR : Reader m n' N p cfg first c bsR)
    (hbq : bsR = E ++ bl :: rest) (hE : AllE E) (hi : bl[i]? = some (a :: t))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) (hpar : fs.par = p) :
    first = false ∧ fs.pc = m + 1 ∧
      msOf bl = tails m (!p) cfg.tape (List.range' c (2 ^ m - c)) ∧
      (∀ b ∈ rest, FreshBlock m n' N (!p) b) ∧
      ∃ c', c ≤ c' ∧ c' < 2 ^ m ∧ a = .rv (!p) (cfg.tape c') ∧
        t = rbsL (!p) 0 m (bitsOf c') := by
  have hne : fs.par ≠ !p := by rw [hpar]; cases p <;> simp
  cases first
  · obtain ⟨hms, hrest⟩ := pickR (hR.2 rfl) hbq hE hi happ hne
    have hv := mem_msOf_of_get hi (List.cons_ne_nil _ _)
    rw [hms] at hv
    obtain ⟨c', hc', he⟩ := mem_tails hv
    rw [List.mem_range'_1] at hc'
    rw [tl_eq] at he
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact ⟨rfl, ((app_rv m n' ι N w fs).1 happ).1, hms, hrest, c', hc'.1, by omega, rfl, rfl⟩
  · exact (pickAllFresh (hR.1 rfl) hbq hi happ hne).elim

/-- The reader cannot fire away from the program counter `m + 1`. -/
theorem reader_no_fire {p : Bool} {cfg : Config Q Γ} {first : Bool} {c : ℕ}
    {bsR E rest : List (List (List (Act Q Γ)))} {bl : List (List (Act Q Γ))} {i : ℕ}
    {a : Act Q Γ} {t : List (Act Q Γ)} (hR : Reader m n' N p cfg first c bsR)
    (hbq : bsR = E ++ bl :: rest) (hE : AllE E) (hi : bl[i]? = some (a :: t))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) (hpar : fs.par = p)
    (hpc : fs.pc ≠ m + 1) : False :=
  hpc (reader_fire hR hbq hE hi happ hpar).2.1

end SpaceEnc

end HTN
