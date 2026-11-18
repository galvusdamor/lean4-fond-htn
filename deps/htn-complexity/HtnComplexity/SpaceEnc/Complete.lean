import HtnComplexity.SpaceEnc.CompYield
/-!
# Completeness of the encoding

**`HTN.SpaceEnc.solvable_of_accepts`**: if the machine accepts the input in space `2 ^ m`, the
encoding is solvable.  The planned run (`HtnComplexity/SpaceEnc/CompPlan.lean`) gives an
executable interleaving of the planned blocks and finish word; the planned blocks are good
blocks (valid chain data, valid head moves) and the finish word starts with an accepting state,
so `boot` followed by this interleaving is a refinement of the root
(`HtnComplexity/SpaceEnc/CompYield.lean`).
-/

namespace HTN

namespace SpaceEnc

open TM Domain

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] {m n' : ℕ} {N : NTM Q Γ}

theorem mem_transL {q : Q} {g : Γ} {q' : Q} {g' : Γ} {μ : Move} :
    (q, g, q', g', μ) ∈ transL N ↔ (q', g', μ) ∈ N.step q g := by
  classical
  simp only [transL, List.mem_filter, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ,
    true_and, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    exact ⟨⟨(q, g, q', g'), μ, mem_allMoves μ, rfl⟩, h⟩

theorem mem_accL {q : Q} : q ∈ accL N ↔ q ∈ N.accept := by
  classical
  simp [accL]

section Plan

variable {ι : Bool → Γ} {w : List Bool} (R : RunSeq N (2 ^ m) (N.initConfig (w.map ι)))

/-- The planned chain data are valid. -/
theorem validCD_cdOf {k c : ℕ} (hk : k < R.r) (hc : c < 2 ^ m) :
    ValidCD m n' N (parR k) (cdOf R m n' w k c) := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases hk0 : k = 0
    · subst hk0
      refine Or.inr ⟨rfl, ?_⟩
      by_cases hcn : c < n'
      · exact Or.inr ⟨c, w.getD c false, hcn, by simp [cdOf, hcn]⟩
      · exact Or.inl (by simp [cdOf, hcn])
    · exact Or.inl (by simp [cdOf, hk0])
  · by_cases hch : c = (R.cf k).head
    · refine Or.inr ⟨((R.cf k).state, (R.cf k).tape c, (R.tr k).1, (R.tr k).2.1, (R.tr k).2.2),
        ?_, by simp [cdOf, hch], by simp [cdOf, hch]⟩
      rw [mem_transL, hch]
      exact R.tr_mem k hk
    · exact Or.inl ⟨(R.cf k).tape c, by simp [cdOf, hch], by simp [cdOf, hch]⟩
  · by_cases hcW : c + 1 = 2 ^ m
    · exact Or.inr (by simp [cdOf, hcW])
    · exact Or.inl ⟨lzb c, lzb_lt hc hcW, by simp [cdOf, hcW]⟩

/-- The planned head move is a method body. -/
theorem hOf_mem {k : ℕ} (hk : k < R.r) :
    (Cmp.reT (parR k), [[aT (hOf R k)]]) ∈ bodies m n' N := by
  have hnext : (R.cf (k + 1)).head = (R.tr k).2.2.apply (R.cf k).head := by
    rw [R.cf_succ k hk]; rfl
  have hlt1 := R.head_lt (k + 1) hk
  have hlt0 := R.head_lt k hk.le
  unfold hOf
  cases hμ : (R.tr k).2.2 with
  | left =>
    dsimp only
    split_ifs with h0
    · simp [bodies, bodiesP]
    · have hl := lob_lt hlt0 h0
      simp [bodies, bodiesP, hl]
  | stay => simp [bodies, bodiesP]
  | right =>
    rw [hμ] at hnext
    simp only [Move.apply] at hnext
    have hl := lzb_lt hlt0 (by omega : (R.cf k).head + 1 ≠ 2 ^ m)
    simp [bodies, bodiesP, hl]

/-- The planned block of a round is a good block. -/
theorem goodBlock_blk {k : ℕ} (hk : k < R.r) : GoodBlock m n' N (parR k) (blk R m n' w k) := by
  refine ⟨(List.range (2 ^ m)).map (cdOf R m n' w k), hOf R k, by simp, ?_, hOf_mem R hk, ?_⟩
  · intro cd hcd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hcd
    exact validCD_cdOf R hk (List.mem_range.1 hc)
  · simp [blk]

/-- The planned future blocks of a loop are good blocks. -/
theorem goodBlock_futB {q : Bool} {k₀ : ℕ} :
    ∀ bl ∈ futB R m n' w q k₀, GoodBlock m n' N q bl := by
  intro bl hbl
  simp only [futB, List.mem_map, List.mem_filter, List.mem_range'_1, beq_iff_eq] at hbl
  obtain ⟨k, ⟨⟨hk0, hk⟩, rfl⟩, rfl⟩ := hbl
  exact goodBlock_blk R (by omega)

end Plan

variable [DecidableEq Q] [DecidableEq Γ]

/-- **Completeness**: if the machine accepts the input in space `2 ^ m`, the encoding is
solvable. -/
theorem solvable_of_accepts {ι : Bool → Γ} {w : List Bool} (hn' : n' = w.length)
    (h : N.AcceptsInSpace (w.map ι) (2 ^ m)) : (prob m n' ι N w).Solvable := by
  obtain ⟨n, c, hreach, hacc⟩ := h
  obtain ⟨R, hr, hcf⟩ := exists_runSeq n _ c hreach
  obtain ⟨z, hG, hseq⟩ := exists_exec_plan (ι := ι) R hn'
  have hq : (R.cf R.r).state ∈ accL N := by rw [mem_accL, hr, hcf]; exact hacc
  have hD : (prob m n' ι N w).domain.methods = methodsOf m n' N := rfl
  have hy : (prob m n' ι N w).domain.ChainYield [cT .root] (.boot :: z) :=
    chain_root_of_gen hD (goodBlock_futB R) (goodBlock_futB R) hq hG
  refine Problem.solvable_iff_netYield.2 ⟨.boot :: z,
    (netYield_grid_iff (grid_of_methodsOf hD)).2 (gridYield_singleton_iff.2 hy), ⟨?_, ?_⟩, ?_⟩
  · show (am m n' ι N).Applicable _ _
    rw [applicable_iff]
    intro f hf
    simp only [precL, List.mem_singleton] at hf
    subst hf
    simp [prob]
  · have htr : (prob m n' ι N w).transition .boot (prob m n' ι N w).init = enc m w (fs0 N) :=
      trans_boot
    show (am m n' ι N).SeqApplicable z ((prob m n' ι N w).transition .boot
      (prob m n' ι N w).init)
    rw [htr]; exact hseq
  · intro f hf
    simp [prob] at hf

/-- **Correctness of the encoding**: the encoding of the input `w` is solvable iff the machine
accepts `w` in space `2 ^ m`. -/
theorem solvable_iff_accepts {ι : Bool → Γ} {w : List Bool} (hn' : n' = w.length) :
    (prob m n' ι N w).Solvable ↔ N.AcceptsInSpace (w.map ι) (2 ^ m) :=
  ⟨accepts_of_solvable hn', solvable_of_accepts hn'⟩

end SpaceEnc

end HTN
