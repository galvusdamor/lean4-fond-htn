import ComplexityTheory.Petri.Pump
/-!
# The rank of generalised problems

The rank of a block is the lexicographic quadruple (maximal number of `ω`s in a label, number of
edges, number of nodes, number of `ω`s in the input and output); the rank of a generalised problem
is the multiset of the ranks of its blocks, ordered by the Dershowitz–Manna ordering, which is
well founded.  Every decomposition step replaces a block by blocks of smaller rank, and preserves
well-formedness (`Inv`).
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp Classical

variable {ι : Type*} [Fintype ι]

/-- The maximal number of `ω`s in a label of a node. -/
noncomputable def maxTop (C : Comp ι) : ℕ := (C.nodes.map fun u => topCount (C.lab u)).foldr max 0

theorem le_foldr_max {l : List ℕ} {f : ℕ → ℕ} {u : ℕ} (hu : u ∈ l) :
    f u ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at hu
  | cons v vs ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hu with rfl | hu
    · exact le_max_left _ _
    · exact (ih hu).trans (le_max_right _ _)

theorem foldr_max_le {l : List ℕ} {f : ℕ → ℕ} {K : ℕ} (h : ∀ u ∈ l, f u ≤ K) :
    (l.map f).foldr max 0 ≤ K := by
  induction l with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h v (by simp)) (ih fun u hu => h u (by simp [hu]))

theorem foldr_max_lt {l : List ℕ} {f : ℕ → ℕ} {K : ℕ} (h : ∀ u ∈ l, f u < K) (hK : 0 < K) :
    (l.map f).foldr max 0 < K := by
  induction l with
  | nil => simpa using hK
  | cons v vs ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_lt (h v (by simp)) (ih fun u hu => h u (by simp [hu]))

theorem le_maxTop {C : Comp ι} {u : ℕ} (hu : u ∈ C.nodes) : topCount (C.lab u) ≤ maxTop C :=
  le_foldr_max (f := fun u => topCount (C.lab u)) hu

theorem maxTop_le {C : Comp ι} {K : ℕ} (h : ∀ u ∈ C.nodes, topCount (C.lab u) ≤ K) :
    maxTop C ≤ K := foldr_max_le h

theorem maxTop_lt {C : Comp ι} {K : ℕ} (h : ∀ u ∈ C.nodes, topCount (C.lab u) < K)
    (hK : 0 < K) : maxTop C < K := foldr_max_lt h hK

/-- The rank of a block. -/
noncomputable def brank (b : Block ι) : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (maxTop b.comp, toLex (b.comp.edges.length,
    toLex (b.comp.nodes.length, topCount b.inp + topCount b.out)))

theorem lex4_lt {a b c d a' b' c' d' : ℕ} (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c')
    (h : a < a' ∨ b < b' ∨ c < c' ∨ d < d') :
    toLex (a, toLex (b, toLex (c, d))) < toLex (a', toLex (b', toLex (c', d'))) := by
  simp only [Prod.Lex.toLex_lt_toLex]
  omega

theorem brank_lt {g b : Block ι} (h1 : maxTop g.comp ≤ maxTop b.comp)
    (h2 : g.comp.edges.length ≤ b.comp.edges.length) (h3 : g.comp.nodes.length ≤ b.comp.nodes.length)
    (h : maxTop g.comp < maxTop b.comp ∨ g.comp.edges.length < b.comp.edges.length ∨
      g.comp.nodes.length < b.comp.nodes.length ∨
      topCount g.inp + topCount g.out < topCount b.inp + topCount b.out) : brank g < brank b :=
  lex4_lt h1 h2 h3 h

/-- The rank of a generalised problem. -/
noncomputable def grank (bs : List (Block ι)) : Multiset (ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ) :=
  ((bs.map brank : List _) : Multiset _)

theorem grank_lt (pre post A : List (Block ι)) (b : Block ι) (hA : ∀ g ∈ A, brank g < brank b) :
    Multiset.IsDershowitzMannaLT (grank (pre ++ A ++ post)) (grank (pre ++ b :: post)) := by
  refine ⟨grank pre + grank post, grank A, {brank b}, by simp, ?_, ?_, ?_⟩
  · simp only [grank, List.map_append, ← Multiset.coe_add]; abel
  · simp only [grank, List.map_append, List.map_cons, ← Multiset.coe_add, ← Multiset.cons_coe]
    rw [Multiset.add_cons, ← Multiset.singleton_add, add_comm]
  · intro y hy
    simp only [grank, Multiset.mem_coe, List.mem_map] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨brank b, by simp, hA g hg⟩

/-- The invariant of the blocks of a generalised problem. -/
def Inv (b : Block ι) : Prop := WFB b ∧ b.comp.edges.Nodup

end KLM

end Petri

end HTN
