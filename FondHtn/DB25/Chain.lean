import FondHtn.DB25.WinK
import FondHtn.Prim.WeakMem
/-!
# Fixed-method strong OD for regular problems with one compound task: the chain game

Let `P` be a problem whose initial network and all method networks are **loops** (all tasks
primitive except one compound task named `c`, which comes after all of them) or **finals** (all
tasks primitive), all methods decomposing `c`.  A fixed-method solution chooses a word of loop
methods `m₁ … m_k` and a final method `f` before execution; the achievable primitive network is
then the series composition of the primitive parts (`FOND.Problem.primPart`) of `tn_I`, `m₁`, …,
`m_k` and `f`, executed layer after layer.

* `FOND.Problem.strongOD_iff_chain` — strong OD plan existence of such a problem is
  `∃ m₁ … m_k f, chainWin [pre, m₁, …, m_k, f] s_I`, where `chainWin` nests the terminal
  conditions of `WinK` (`FOND.Problem.chainWin`).

The proof tracks a layer function through decompositions (`FOND.Problem.Layered`).
-/

namespace FOND

open HTN FOND.TaskNetwork

namespace Problem

variable {F A C I : Type} [DecidableEq I]

open Classical in
/-- The primitive part of a network. -/
noncomputable def primPart (tn : HTN.TaskNetwork I A C) : HTN.TaskNetwork I A C :=
  restr tn fun x => ∃ a, tn.α x = Sum.inl a

/-- A loop network: one compound task `c`, after all other (primitive) tasks. -/
def IsLoop (tn : HTN.TaskNetwork I A C) (c : C) : Prop :=
  tn.WF ∧ ∃ t₀ ∈ tn.T, tn.α t₀ = Sum.inr c ∧
    ∀ t ∈ tn.T, t ≠ t₀ → (∃ a, tn.α t = Sum.inl a) ∧ tn.ord t t₀

/-- A final network: all tasks primitive. -/
def IsFinal (tn : HTN.TaskNetwork I A C) : Prop := tn.WF ∧ tn.IsPrimitive

/-- The problem is a regular chain problem for the compound name `c`. -/
structure RegChain (P : Problem F A C I) (c : C) : Prop where
  tnI : IsLoop P.tnI c
  methods : ∀ m ∈ P.methods, m.abstractTask = c ∧ (IsLoop m.subtasks c ∨ IsFinal m.subtasks)

/-- **The chain game**: the layers are executed one after the other. -/
def chainWin (P : Problem F A C I) : List (HTN.TaskNetwork I A C) → Set F → Prop
  | [], _ => True
  | X :: L, s => P.WinK (chainWin P L) X s

/-! ## Isomorphisms of restrictions -/

theorem isoVia_restr {σ : I → I} {u v : HTN.TaskNetwork I A C} (h : HTN.TaskNetwork.IsoVia σ u v)
    {S S' : I → Prop} [DecidablePred S] [DecidablePred S'] (hS : ∀ x ∈ u.T, S x ↔ S' (σ x)) :
    HTN.TaskNetwork.IsoVia σ (restr u S) (restr v S') := by
  refine ⟨⟨fun x hx => ?_, fun x hx y hy he => ?_, fun y hy => ?_⟩, fun a ha b hb => ?_,
    fun a ha => ?_⟩
  · obtain ⟨hx1, hx2⟩ := (mem_restr_T u S).1 hx
    exact (mem_restr_T v S').2 ⟨h.mem hx1, (hS x hx1).1 hx2⟩
  · exact h.inj ((mem_restr_T u S).1 hx).1 ((mem_restr_T u S).1 hy).1 he
  · obtain ⟨hy1, hy2⟩ := (mem_restr_T v S').1 hy
    obtain ⟨x, hx, rfl⟩ := h.surj hy1
    exact ⟨x, (mem_restr_T u S).2 ⟨hx, (hS x hx).2 hy2⟩, rfl⟩
  · have ha' := ((mem_restr_T u S).1 ha).1
    have hb' := ((mem_restr_T u S).1 hb).1
    simp only [restr]
    rw [h.2.1 a ha' b hb', hS a ha', hS b hb']
  · exact h.2.2 a ((mem_restr_T u S).1 ha).1

theorem isoVia_id_of_sameOn {u v : HTN.TaskNetwork I A C} (h : SameOn u v) :
    HTN.TaskNetwork.IsoVia id u v := by
  obtain ⟨hT, ho, hα⟩ := h
  refine ⟨?_, fun a ha b hb => ho a ha b hb, fun a ha => hα a ha⟩
  rw [hT]; exact Set.bijOn_id _

/-! ## Layers -/

/-- `N` consists of the primitive layers `L` (and, if `op`, a last layer with one compound
task `c`). -/
def Layered (N : HTN.TaskNetwork I A C) (c : C) (L : List (HTN.TaskNetwork I A C)) (op : Bool) :
    Prop :=
  ∃ lay : I → ℕ,
    (∀ a ∈ N.T, lay a ≤ L.length) ∧
    (∀ a ∈ N.T, ∀ b ∈ N.T, lay a < lay b → N.ord a b) ∧
    (∀ a ∈ N.T, ∀ b ∈ N.T, N.ord a b → lay a ≤ lay b) ∧
    (∀ i (hi : i < L.length), (restr N fun x => lay x = i).Iso L[i]) ∧
    (∀ a ∈ N.T, lay a < L.length → ∃ x, N.α a = Sum.inl x) ∧
    (∀ a ∈ N.T, lay a = L.length → op = true ∧ N.α a = Sum.inr c) ∧
    (op = true → ∃ t₀ ∈ N.T, lay t₀ = L.length ∧ ∀ a ∈ N.T, lay a = L.length → a = t₀)

variable {P : Problem F A C I}

theorem iso_prim {u v : HTN.TaskNetwork I A C} (h : u.Iso v) (hv : ∀ x ∈ v.T, ∃ a, v.α x = Sum.inl a) :
    ∀ x ∈ u.T, ∃ a, u.α x = Sum.inl a := by
  obtain ⟨σ, hσ⟩ := h
  have hσ : HTN.TaskNetwork.IsoVia σ u v := hσ
  intro x hx
  obtain ⟨a, ha⟩ := hv _ (hσ.mem hx)
  exact ⟨a, by rw [hσ.2.2 x hx]; exact ha⟩

/-- A chain of primitive layers is solved iff the chain game is won. -/
theorem beliefSolvable_iff_chainWin [Nonempty I] : ∀ (L : List (HTN.TaskNetwork I A C))
    (N : HTN.TaskNetwork I A C) (c : C) (s : Set F), Layered N c L false →
    (P.BeliefSolvable N s ↔ P.chainWin L s) := by
  classical
  intro L
  induction L with
  | nil =>
    rintro N c s ⟨lay, hle, -, -, -, -, htop, -⟩
    have hE : N.T = ∅ := by
      ext a; simp only [Finset.notMem_empty, iff_false]
      intro ha
      have := htop a ha (by simpa using hle a ha)
      simp at this
    simp only [chainWin, iff_true]
    exact .empty hE
  | cons X L ih =>
    rintro N c s ⟨lay, hle, hlt, hord, hiso, hprim, htop, hone⟩
    rw [← winK_true_iff]
    have hB : Before (fun x => lay x = 0) N :=
      ⟨fun a ha b hb h0 h1 => hlt a ha b hb (by omega),
       fun a ha b hb h0 h1 hab => by have := hord a ha b hb hab; omega⟩
    rw [winK_split _ hB]
    have hX : (restr N fun x => lay x = 0).Iso X := by simpa using hiso 0 (by simp)
    have hrest : Layered (restr N fun x => ¬ lay x = 0) c L false := by
      refine ⟨fun x => lay x - 1, fun a ha => ?_, fun a ha b hb h => ?_, fun a ha b hb h => ?_,
        fun i hi => ?_, fun a ha h => ?_, fun a ha h => ?_, fun h => by simp at h⟩ <;>
        dsimp only at *
      · have := hle a ((mem_restr_T _ _).1 ha).1; simp at this; omega
      · obtain ⟨ha1, ha2⟩ := (mem_restr_T _ _).1 ha
        obtain ⟨hb1, hb2⟩ := (mem_restr_T _ _).1 hb
        exact ⟨hlt a ha1 b hb1 (by omega), ha2, hb2⟩
      · have := hord a ((mem_restr_T _ _).1 ha).1 b ((mem_restr_T _ _).1 hb).1 h.1; omega
      · have h1 := hiso (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at h1
        refine HTN.TaskNetwork.Iso.trans (tn₂ := restr N fun x => lay x = i + 1)
          ⟨id, isoVia_id_of_sameOn ⟨?_, fun a ha b hb => ?_, fun _ _ => rfl⟩⟩ h1
        · ext x; simp only [mem_restr_T]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, by omega⟩
        · simp only [mem_restr_T] at ha hb
          obtain ⟨⟨-, ha2⟩, ha3⟩ := ha
          obtain ⟨⟨-, hb2⟩, hb3⟩ := hb
          simp only [restr]
          constructor
          · rintro ⟨⟨h, -, -⟩, -, -⟩; exact ⟨h, by omega, by omega⟩
          · rintro ⟨h, -, -⟩; exact ⟨⟨h, ha2, hb2⟩, by omega, by omega⟩
      · obtain ⟨ha1, ha2⟩ := (mem_restr_T _ _).1 ha
        exact hprim a ha1 (by simp; omega)
      · obtain ⟨ha1, ha2⟩ := (mem_restr_T _ _).1 ha
        have := htop a ha1 (by have := hle a ha1; simp at this ⊢; omega)
        simp at this
    have hK : P.WinK (fun _ => True) (restr N fun x => ¬ lay x = 0) =
        P.chainWin L := funext fun s' => propext ((winK_true_iff).trans (ih _ c s' hrest))
    rw [hK, chainWin]
    exact ⟨fun h => h.iso hX, fun h => h.iso hX.symm⟩

/-! ## Decomposition steps preserve the layers -/

theorem loop_of_iso [Nonempty I] {u v : HTN.TaskNetwork I A C} {c : C} (h : u.Iso v)
    (hu : u.WF) (hv : IsLoop v c) : IsLoop u c := by
  obtain ⟨σ, hσ⟩ := h
  have hσ : HTN.TaskNetwork.IsoVia σ u v := hσ
  obtain ⟨-, t₀, ht₀, hα₀, hrest⟩ := hv
  obtain ⟨t, ht, rfl⟩ := hσ.surj ht₀
  refine ⟨hu, t, ht, by rw [hσ.2.2 t ht]; exact hα₀, fun x hx hxt => ?_⟩
  have hne : σ x ≠ σ t := fun he => hxt (hσ.inj hx ht he)
  obtain ⟨⟨a, ha⟩, hord⟩ := hrest _ (hσ.mem hx) hne
  exact ⟨⟨a, by rw [hσ.2.2 x hx]; exact ha⟩, (hσ.2.1 x hx t ht).2 hord⟩

theorem final_of_iso {u v : HTN.TaskNetwork I A C} (h : u.Iso v) (hu : u.WF) (hv : IsFinal v) :
    IsFinal u :=
  ⟨hu, fun x hx => iso_prim h (fun y hy => hv.2 y hy) x hx⟩

theorem primPart_iso {u v : HTN.TaskNetwork I A C} (h : u.Iso v) :
    (primPart u).Iso (primPart v) := by
  classical
  obtain ⟨σ, hσ⟩ := h
  have hσ : HTN.TaskNetwork.IsoVia σ u v := hσ
  refine ⟨σ, isoVia_restr hσ fun x hx => ?_⟩
  rw [hσ.2.2 x hx]

open Classical in
theorem primPart_final {u : HTN.TaskNetwork I A C} (h : IsFinal u) : (primPart u).Iso u := by
  classical
  refine ⟨id, isoVia_id_of_sameOn ⟨?_, fun a ha b hb => ?_, fun _ _ => rfl⟩⟩
  · ext x; simp only [primPart, mem_restr_T]; exact ⟨fun h => h.1, fun hx => ⟨hx, h.2 x hx⟩⟩
  · simp only [primPart, mem_restr_T] at ha hb
    simp only [primPart, restr]
    exact ⟨fun h => h.1, fun h => ⟨h, ha.2, hb.2⟩⟩

theorem layered_congr_last {N : HTN.TaskNetwork I A C} {c : C} {L : List (HTN.TaskNetwork I A C)}
    {B B' : HTN.TaskNetwork I A C} {op : Bool} (h : Layered N c (L ++ [B]) op) (hB : B.Iso B') :
    Layered N c (L ++ [B']) op := by
  obtain ⟨lay, hle, hlt, hord, hiso, hprim, htop, hone⟩ := h
  refine ⟨lay, by simpa using hle, hlt, hord, fun i hi => ?_, by simpa using hprim,
    by simpa using htop, by simpa using hone⟩
  have := hiso i (by simpa using hi)
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i L.length with h | h
  · rw [List.getElem_append_left h] at this ⊢; exact this
  · have hi' : i = L.length := by omega
    subst hi'
    simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton] at this ⊢
    exact this.trans hB

open Classical in
/-- Decomposing the top task of an open layered network by a loop or final network. -/
theorem layered_decompose {N u : HTN.TaskNetwork I A C} {c : C} {L : List (HTN.TaskNetwork I A C)}
    {t : I} (hN : Layered N c L true) (hwf : N.WF) (hu : u.WF) (hdisj : Disjoint N.T u.T)
    (htT : t ∈ N.T) (hαt : ∃ c', N.α t = Sum.inr c') (hshape : IsLoop u c ∨ IsFinal u) :
    Layered (decomposeWith N t u) c (L ++ [primPart u]) (decide (IsLoop u c)) := by
  obtain ⟨lay, hle, hlt, hord, hiso, hprim, htop, hone⟩ := hN
  have hlayt : lay t = L.length := by
    by_contra hne
    obtain ⟨x, hx⟩ := hprim t htT (lt_of_le_of_ne (hle t htT) hne)
    obtain ⟨c', hc'⟩ := hαt
    rw [hc'] at hx; cases hx
  obtain ⟨t₀, -, -, huniq⟩ := hone rfl
  have hold : ∀ a ∈ N.T, a ≠ t → lay a < L.length := fun a ha hat => by
    rcases lt_or_eq_of_le (hle a ha) with h | h
    · exact h
    · exact absurd ((huniq a ha h).trans (huniq t htT hlayt).symm) hat
  have hnu : ∀ a ∈ N.T, a ∉ u.T := fun a ha => Finset.disjoint_left.1 hdisj ha
  have hnN : ∀ a ∈ u.T, a ∉ N.T := fun a ha h => hnu a h ha
  let Q : I → Prop := fun x => ∃ a, u.α x = Sum.inl a
  let lay' : I → ℕ := fun x => if x ∈ u.T then (if Q x then L.length else L.length + 1) else lay x
  have hlo : ∀ a ∈ N.T, lay' a = lay a := fun a ha => by simp [lay', hnu a ha]
  have hlu : ∀ a ∈ u.T, lay' a = if Q a then L.length else L.length + 1 := fun a ha => by simp [lay', ha]
  -- the compound task of `u` is maximal
  have hloop_ord : IsLoop u c → ∀ a ∈ u.T, ∀ b ∈ u.T, ¬ Q a → Q b → ¬ u.ord a b := by
    rintro ⟨-, t₁, ht₁, hα₁, hr⟩ a ha b hb hQa hQb hab
    have ha1 : a = t₁ := by
      by_contra hne; exact hQa (hr a ha hne).1
    subst ha1
    have hbt : b ≠ a := fun e => by subst e; exact hQa hQb
    exact hu.irrefl _ (hu.trans hab (hr b hb hbt).2)
  have hfinQ : IsFinal u → ∀ a ∈ u.T, Q a := fun h a ha => h.2 a ha
  refine ⟨lay', fun a ha => ?_, fun a ha b hb hab => ?_, fun a ha b hb hab => ?_,
    fun i hi => ?_, fun a ha hlt' => ?_, fun a ha heq => ?_, fun _ => ?_⟩
  · simp only [List.length_append, List.length_singleton]
    rcases mem_decomposeWith_T.1 ha with ⟨ha1, ha2⟩ | ha1
    · rw [hlo a ha1]; have := hold a ha1 ha2; omega
    · rw [hlu a ha1]; split_ifs <;> omega
  · rcases mem_decomposeWith_T.1 ha with ⟨ha1, ha2⟩ | ha1 <;>
      rcases mem_decomposeWith_T.1 hb with ⟨hb1, hb2⟩ | hb1
    · rw [hlo a ha1, hlo b hb1] at hab
      exact (decomposeWith_ord_old_old hu hdisj ha1 ha2 hb1 hb2).2 (hlt a ha1 b hb1 hab)
    · exact (decomposeWith_ord_old_new hwf hu hdisj ha1 hb1).2
        (hlt a ha1 t htT (by rw [hlayt]; exact hold a ha1 ha2))
    · rw [hlu a ha1, hlo b hb1] at hab; have := hold b hb1 hb2; split_ifs at hab <;> omega
    · rw [hlu a ha1, hlu b hb1] at hab
      refine (decomposeWith_ord_new_new hwf hdisj ha1 hb1).2 ?_
      by_cases hQa : Q a <;> by_cases hQb : Q b <;> simp only [hQa, hQb, if_true, if_false] at hab
      · omega
      · rcases hshape with ⟨-, t₁, ht₁, hα₁, hr⟩ | hf
        · have hbt : b = t₁ := by by_contra hne; exact hQb (hr b hb1 hne).1
          subst hbt
          exact (hr a ha1 (fun e => by subst e; exact hQb hQa)).2
        · exact absurd (hfinQ hf b hb1) hQb
      · omega
      · omega
  · rcases mem_decomposeWith_T.1 ha with ⟨ha1, ha2⟩ | ha1 <;>
      rcases mem_decomposeWith_T.1 hb with ⟨hb1, hb2⟩ | hb1
    · rw [hlo a ha1, hlo b hb1]
      exact hord a ha1 b hb1 ((decomposeWith_ord_old_old hu hdisj ha1 ha2 hb1 hb2).1 hab)
    · rw [hlo a ha1, hlu b hb1]; have := hold a ha1 ha2; split_ifs <;> omega
    · have h1 := (decomposeWith_ord_new_old hwf hu hdisj ha1 hb1).1 hab
      have := hord t htT b hb1 h1
      exact absurd (huniq b hb1 (by have := hle b hb1; omega)) (fun e => hb2 (e.trans
        (huniq t htT hlayt).symm))
    · rw [hlu a ha1, hlu b hb1]
      have h1 := (decomposeWith_ord_new_new hwf hdisj ha1 hb1).1 hab
      by_cases hQa : Q a <;> by_cases hQb : Q b <;> simp only [hQa, hQb, if_true, if_false]
      · omega
      · omega
      · rcases hshape with hl | hf
        · exact absurd h1 (hloop_ord hl a ha1 b hb1 hQa hQb)
        · exact absurd (hfinQ hf a ha1) hQa
      · omega
  · simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i L.length with h | h
    · rw [List.getElem_append_left h]
      refine HTN.TaskNetwork.Iso.trans ⟨id, isoVia_id_of_sameOn ⟨?_, fun a ha b hb => ?_, fun a ha => ?_⟩⟩
        (hiso i h)
      · ext x
        simp only [mem_restr_T, mem_decomposeWith_T]
        constructor
        · rintro ⟨⟨hx1, hx2⟩ | hx1, hx3⟩
          · rw [hlo x hx1] at hx3; exact ⟨hx1, hx3⟩
          · rw [hlu x hx1] at hx3; split_ifs at hx3 <;> omega
        · rintro ⟨hx1, hx2⟩
          refine ⟨Or.inl ⟨hx1, fun e => ?_⟩, by rw [hlo x hx1]; exact hx2⟩
          subst e; omega
      · simp only [mem_restr_T, mem_decomposeWith_T] at ha hb
        simp only [restr]
        have ha' : a ∈ N.T ∧ a ≠ t := by
          rcases ha.1 with h1 | h1
          · exact h1
          · have := ha.2; rw [hlu a h1] at this; split_ifs at this <;> omega
        have hb' : b ∈ N.T ∧ b ≠ t := by
          rcases hb.1 with h1 | h1
          · exact h1
          · have := hb.2; rw [hlu b h1] at this; split_ifs at this <;> omega
        rw [decomposeWith_ord_old_old hu hdisj ha'.1 ha'.2 hb'.1 hb'.2, hlo a ha'.1, hlo b hb'.1]
      · simp only [mem_restr_T, mem_decomposeWith_T] at ha
        simp only [restr, decomposeWith_α]
        have : a ∉ u.T := by
          rcases ha.1 with h1 | h1
          · exact hnu a h1.1
          · have := ha.2; rw [hlu a h1] at this; split_ifs at this <;> omega
        simp [this]
    · have hi' : i = L.length := by omega
      subst hi'
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton]
      refine ⟨id, isoVia_id_of_sameOn ⟨?_, fun a ha b hb => ?_, fun a ha => ?_⟩⟩
      · ext x
        simp only [mem_restr_T, mem_decomposeWith_T, primPart]
        constructor
        · rintro ⟨⟨hx1, hx2⟩ | hx1, hx3⟩
          · rw [hlo x hx1] at hx3; exact absurd hx3 (by have := hold x hx1 hx2; omega)
          · rw [hlu x hx1] at hx3
            by_cases hq : Q x
            · exact ⟨hx1, hq⟩
            · rw [if_neg hq] at hx3; omega
        · rintro ⟨hx1, hx2⟩
          exact ⟨Or.inr hx1, by rw [hlu x hx1, if_pos hx2]⟩
      · simp only [primPart, mem_restr_T, mem_decomposeWith_T] at ha hb
        simp only [primPart, restr]
        have ha' : a ∈ u.T := by
          rcases ha.1 with h1 | h1
          · have := ha.2; rw [hlo a h1.1] at this; have := hold a h1.1 h1.2; omega
          · exact h1
        have hb' : b ∈ u.T := by
          rcases hb.1 with h1 | h1
          · have := hb.2; rw [hlo b h1.1] at this; have := hold b h1.1 h1.2; omega
          · exact h1
        have hQa : Q a := by have := ha.2; rw [hlu a ha'] at this; by_contra hq; rw [if_neg hq] at this; omega
        have hQb : Q b := by have := hb.2; rw [hlu b hb'] at this; by_contra hq; rw [if_neg hq] at this; omega
        rw [decomposeWith_ord_new_new hwf hdisj ha' hb']
        exact ⟨fun h => ⟨h.1, hQa, hQb⟩, fun h => ⟨h.1, by rw [hlu a ha', if_pos hQa],
          by rw [hlu b hb', if_pos hQb]⟩⟩
      · simp only [primPart, mem_restr_T, mem_decomposeWith_T] at ha
        simp only [primPart, restr, decomposeWith_α]
        have ha' : a ∈ u.T := by
          rcases ha.1 with h1 | h1
          · have := ha.2; rw [hlo a h1.1] at this; have := hold a h1.1 h1.2; omega
          · exact h1
        simp [ha']
  · simp only [List.length_append, List.length_singleton] at hlt'
    rcases mem_decomposeWith_T.1 ha with ⟨ha1, ha2⟩ | ha1
    · obtain ⟨x, hx⟩ := hprim a ha1 (hold a ha1 ha2)
      exact ⟨x, by simp [hnu a ha1, hx]⟩
    · rw [hlu a ha1] at hlt'
      by_cases hq : Q a
      · obtain ⟨x, hx⟩ := hq; exact ⟨x, by simp [ha1, hx]⟩
      · rw [if_neg hq] at hlt'; omega
  · simp only [List.length_append, List.length_singleton] at heq
    rcases mem_decomposeWith_T.1 ha with ⟨ha1, ha2⟩ | ha1
    · rw [hlo a ha1] at heq; have := hold a ha1 ha2; omega
    · rw [hlu a ha1] at heq
      have hq : ¬ Q a := fun hq => by rw [if_pos hq] at heq; omega
      rcases hshape with hl | hf
      · obtain ⟨-, t₁, ht₁, hα₁, hr⟩ := hl
        have : a = t₁ := by by_contra hne; exact hq (hr a ha1 hne).1
        subst this
        exact ⟨decide_eq_true ⟨hu, a, ht₁, hα₁, hr⟩, by simp [ha1, hα₁]⟩
      · exact absurd (hfinQ hf a ha1) hq
  · have hl : IsLoop u c := by
      rename_i h; exact of_decide_eq_true h
    obtain ⟨-, t₁, ht₁, hα₁, hr⟩ := hl
    have hQ : ¬ Q t₁ := fun ⟨x, hx⟩ => by rw [hα₁] at hx; cases hx
    refine ⟨t₁, mem_decomposeWith_T.2 (Or.inr ht₁), by
      simp only [List.length_append, List.length_singleton]; rw [hlu t₁ ht₁, if_neg hQ],
      fun a ha heq => ?_⟩
    simp only [List.length_append, List.length_singleton] at heq
    rcases mem_decomposeWith_T.1 ha with ⟨ha1, ha2⟩ | ha1
    · rw [hlo a ha1] at heq; have := hold a ha1 ha2; omega
    · by_contra hne
      have := (hr a ha1 hne).1
      rw [hlu a ha1, if_pos this] at heq; omega

theorem loop_not_final {u : HTN.TaskNetwork I A C} {c : C} (hl : IsLoop u c) : ¬ IsFinal u := by
  rintro ⟨-, hp⟩
  obtain ⟨-, t₀, ht₀, hα₀, -⟩ := hl
  obtain ⟨a, ha⟩ := hp t₀ ht₀
  rw [hα₀] at ha; cases ha

theorem layered_init {c : C} (h : IsLoop P.tnI c) : Layered P.tnI c [primPart P.tnI] true := by
  classical
  obtain ⟨hwf, t₀, ht₀, hα₀, hr⟩ := h
  have hnp : ¬ ∃ a, P.tnI.α t₀ = Sum.inl a := fun ⟨a, ha⟩ => by rw [hα₀] at ha; cases ha
  refine ⟨fun x => if x = t₀ then 1 else 0, fun a ha => ?_, fun a ha b hb hab => ?_,
    fun a ha b hb hab => ?_, fun i hi => ?_, fun a ha hlt => ?_, fun a ha heq => ?_,
    fun _ => ⟨t₀, ht₀, by simp, fun a ha heq => ?_⟩⟩ <;> dsimp only at *
  · split_ifs <;> simp
  · by_cases hb' : b = t₀
    · subst hb'
      have ha' : a ≠ b := fun e => by subst e; simp at hab
      exact (hr a ha ha').2
    · simp [hb'] at hab
  · by_cases ha' : a = t₀
    · subst ha'
      by_cases hb' : b = a
      · subst hb'; exact absurd hab (hwf.irrefl _)
      · exact absurd (hwf.trans hab (hr b hb hb').2) (hwf.irrefl _)
    · simp [ha']
  · obtain rfl : i = 0 := by simpa using hi
    simp only [List.getElem_cons_zero]
    refine ⟨id, isoVia_id_of_sameOn ⟨?_, fun a ha b hb => ?_, fun _ _ => rfl⟩⟩
    · ext x; simp only [mem_restr_T, primPart]
      constructor
      · rintro ⟨hx, hx'⟩
        have : x ≠ t₀ := fun e => by simp [e] at hx'
        exact ⟨hx, (hr x hx this).1⟩
      · rintro ⟨hx, hx'⟩
        have : x ≠ t₀ := fun e => hnp (e ▸ hx')
        exact ⟨hx, by simp [this]⟩
    · simp only [mem_restr_T] at ha hb
      simp only [primPart, restr]
      have ha' : a ≠ t₀ := fun e => by simp [e] at ha
      have hb' : b ≠ t₀ := fun e => by simp [e] at hb
      exact ⟨fun h => ⟨h.1, (hr a ha.1 ha').1, (hr b hb.1 hb').1⟩,
        fun h => ⟨h.1, by simp [ha'], by simp [hb']⟩⟩
  · have : a ≠ t₀ := fun e => by simp [e] at hlt
    exact (hr a ha this).1
  · have : a = t₀ := by by_contra hne; simp [hne] at heq
    subst this
    exact ⟨rfl, hα₀⟩
  · by_contra hne; simp [hne] at heq

/-- Closed layered networks are primitive. -/
theorem layered_closed_prim {N : HTN.TaskNetwork I A C} {c : C} {L : List (HTN.TaskNetwork I A C)}
    (h : Layered N c L false) : N.IsPrimitive := by
  obtain ⟨lay, hle, -, -, -, hprim, htop, -⟩ := h
  intro a ha
  rcases lt_or_eq_of_le (hle a ha) with hlt | heq
  · exact hprim a ha hlt
  · exact absurd (htop a ha heq).1 (by simp)

theorem layered_open_not_prim {N : HTN.TaskNetwork I A C} {c : C}
    {L : List (HTN.TaskNetwork I A C)} (h : Layered N c L true) : ¬ N.IsPrimitive := by
  obtain ⟨lay, -, -, -, -, -, htop, hone⟩ := h
  obtain ⟨t₀, ht₀, hl, -⟩ := hone rfl
  intro hp
  obtain ⟨a, ha⟩ := hp t₀ ht₀
  rw [(htop t₀ ht₀ hl).2] at ha; cases ha

/-- The blocks of a word of loop methods. -/
noncomputable def blocks (ms : List (Method I A C)) : List (HTN.TaskNetwork I A C) :=
  ms.map fun m => primPart m.subtasks

theorem layered_step [Nonempty I] {N N' : HTN.TaskNetwork I A C} {c : C}
    {L : List (HTN.TaskNetwork I A C)} {t : I} {m : Method I A C} (hP : P.RegChain c)
    (hN : Layered N c L true) (hwf : N.WF) (hs : DecompStep P.methods N t m N') :
    (IsLoop m.subtasks c ∧ Layered N' c (L ++ [primPart m.subtasks]) true) ∨
      (IsFinal m.subtasks ∧ Layered N' c (L ++ [m.subtasks]) false) := by
  obtain ⟨hm, htT, hαt, u, hu, huiso, hdisj, rfl⟩ := hs
  obtain ⟨hc, hshape⟩ := hP.methods m hm
  have hd := fun hsh => layered_decompose (u := u) hN hwf hu hdisj htT ⟨_, hαt⟩ hsh
  rcases hshape with hl | hf
  · have hl' := loop_of_iso huiso hu hl
    left
    refine ⟨hl, ?_⟩
    have := layered_congr_last (hd (Or.inl hl')) (primPart_iso huiso)
    simpa [hl'] using this
  · have hf' := final_of_iso huiso hu hf
    right
    refine ⟨hf, ?_⟩
    have := layered_congr_last (hd (Or.inr hf'))
      ((primPart_final hf').trans huiso)
    have hnl : ¬ IsLoop u c := fun h => loop_not_final h hf'
    simpa [hnl] using this

theorem layered_closed_no_step {N N' : HTN.TaskNetwork I A C} {c : C}
    {L : List (HTN.TaskNetwork I A C)} {t : I} {m : Method I A C} (hN : Layered N c L false)
    (hs : DecompStep P.methods N t m N') : False := by
  obtain ⟨-, htT, hαt, -⟩ := hs
  obtain ⟨a, ha⟩ := layered_closed_prim hN t htT
  rw [hαt] at ha; cases ha

/-- Invariant of the networks reachable from `tn_I`. -/
def ChainInv (P : Problem F A C I) (c : C) (N : HTN.TaskNetwork I A C) : Prop :=
  (∃ ms : List (Method I A C), (∀ m ∈ ms, m ∈ P.methods ∧ IsLoop m.subtasks c) ∧
      Layered N c (primPart P.tnI :: blocks ms) true) ∨
    (∃ (ms : List (Method I A C)) (mf : Method I A C),
      (∀ m ∈ ms, m ∈ P.methods ∧ IsLoop m.subtasks c) ∧ mf ∈ P.methods ∧ IsFinal mf.subtasks ∧
        Layered N c (primPart P.tnI :: blocks ms ++ [mf.subtasks]) false)

theorem chainInv_of_decomposesTo [Nonempty I] {c : C} (hP : P.RegChain c) {N : HTN.TaskNetwork I A C}
    (h : P.DecomposesTo P.tnI N) : ChainInv P c N := by
  induction h with
  | refl => exact Or.inl ⟨[], by simp, by simpa [blocks] using layered_init hP.tnI⟩
  | @tail X Y hXY hstep ih =>
    obtain ⟨t, m, hs⟩ := hstep
    have hwf : X.WF := HTN.DecomposesTo.wf hXY hP.tnI.1
    rcases ih with ⟨ms, hms, hl⟩ | ⟨ms, mf, -, -, -, hl⟩
    · have hm := hs.1
      rcases layered_step hP hl hwf hs with ⟨hloop, hl'⟩ | ⟨hfin, hl'⟩
      · refine Or.inl ⟨ms ++ [m], fun m' hm' => ?_, by simpa [blocks] using hl'⟩
        rcases List.mem_append.1 hm' with h | h
        · exact hms m' h
        · obtain rfl : m' = m := by simpa using h
          exact ⟨hm, hloop⟩
      · exact Or.inr ⟨ms, m, hms, hm, hfin, by simpa [blocks] using hl'⟩
    · exact (layered_closed_no_step hl hs).elim

theorem exists_decomp [Nonempty I] [Infinite I] {c : C} (hP : P.RegChain c)
    (mf : Method I A C) (hmf : mf ∈ P.methods) (hfin : IsFinal mf.subtasks) :
    ∀ (ms : List (Method I A C)) (L : List (HTN.TaskNetwork I A C)) (N : HTN.TaskNetwork I A C),
      (∀ m ∈ ms, m ∈ P.methods ∧ IsLoop m.subtasks c) → P.DecomposesTo P.tnI N → N.WF →
      Layered N c L true →
      ∃ N', P.DecomposesTo P.tnI N' ∧ Layered N' c (L ++ blocks ms ++ [mf.subtasks]) false := by
  intro ms
  induction ms with
  | nil =>
    intro L N _ hd hwf hl
    have hl1 := hl
    obtain ⟨lay, -, -, -, -, -, htop, hone⟩ := hl
    obtain ⟨t₀, ht₀, hl0, -⟩ := hone rfl
    obtain ⟨u, hu, huiso, hdisj⟩ := HTN.TaskNetwork.exists_fresh_iso_copy mf.subtasks hfin.1 N.T
    have hstep : DecompStep P.methods N t₀ mf (decomposeWith N t₀ u) :=
      ⟨hmf, ht₀, by rw [(htop t₀ ht₀ hl0).2, (hP.methods mf hmf).1], u, hu, huiso, hdisj, rfl⟩
    refine ⟨_, hd.tail ⟨t₀, mf, hstep⟩, ?_⟩
    rcases layered_step hP hl1 hwf hstep with ⟨hl', -⟩ | ⟨-, hl'⟩
    · exact absurd hfin (loop_not_final hl')
    · simpa [blocks] using hl'
  | cons m ms ih =>
    intro L N hms hd hwf hl
    have hl0 := hl
    obtain ⟨lay, -, -, -, -, -, htop, hone⟩ := hl
    obtain ⟨t₀, ht₀, hlt0, -⟩ := hone rfl
    have hm := hms m (by simp)
    obtain ⟨u, hu, huiso, hdisj⟩ := HTN.TaskNetwork.exists_fresh_iso_copy m.subtasks hm.2.1 N.T
    have hstep : DecompStep P.methods N t₀ m (decomposeWith N t₀ u) :=
      ⟨hm.1, ht₀, by rw [(htop t₀ ht₀ hlt0).2, (hP.methods m hm.1).1], u, hu, huiso, hdisj, rfl⟩
    rcases layered_step hP hl0 hwf hstep with ⟨-, hl'⟩ | ⟨hf, -⟩
    · obtain ⟨N', hd', hl''⟩ := ih (L ++ [primPart m.subtasks]) _
        (fun m' hm' => hms m' (by simp [hm'])) (hd.tail ⟨t₀, m, hstep⟩)
        (decomposeWith_wf hwf hu hdisj) hl'
      exact ⟨N', hd', by simpa [blocks] using hl''⟩
    · exact absurd hf (loop_not_final hm.2)

/-- **Fixed-method strong OD for regular one-compound problems is the chain game.** -/
theorem strongOD_iff_chain [Nonempty I] [Infinite I] {c : C} (hP : P.RegChain c) :
    P.StrongODSolvable ↔ ∃ (ms : List (Method I A C)) (mf : Method I A C),
      (∀ m ∈ ms, m ∈ P.methods ∧ IsLoop m.subtasks c) ∧ mf ∈ P.methods ∧ IsFinal mf.subtasks ∧
        P.chainWin (primPart P.tnI :: blocks ms ++ [mf.subtasks]) P.init := by
  rw [strongODSolvable_iff_fmSolvableDB]
  constructor
  · rintro ⟨N, ⟨hd, hprim⟩, hbs⟩
    rcases chainInv_of_decomposesTo hP hd with ⟨ms, -, hl⟩ | ⟨ms, mf, hms, hmf, hfin, hl⟩
    · exact absurd hprim (layered_open_not_prim hl)
    · exact ⟨ms, mf, hms, hmf, hfin, (beliefSolvable_iff_chainWin _ N c _ hl).1 hbs⟩
  · rintro ⟨ms, mf, hms, hmf, hfin, hw⟩
    obtain ⟨N, hd, hl⟩ := exists_decomp hP mf hmf hfin ms [primPart P.tnI] P.tnI hms
      Relation.ReflTransGen.refl hP.tnI.1 (layered_init hP.tnI)
    have hl' : Layered N c (primPart P.tnI :: blocks ms ++ [mf.subtasks]) false := by
      simpa using hl
    exact ⟨N, ⟨hd, layered_closed_prim hl'⟩, (beliefSolvable_iff_chainWin _ N c _ hl').2 hw⟩

end Problem

end FOND
