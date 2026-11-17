import FondHtn.DB25.Build
/-!
# Regular problems from register programs

`FOND.DB.opDesc V ρ₀ q₀ pre loops finals`: the regular FOND problem whose initial network, loop
methods and final methods are blocks of register operations (`FOND.DB.Op`), with the registers
`V` initially `ρ₀` and the machine state `q₀`.

`FOND.DB.opDesc_strongOD_iff`: strong OD plan existence is
`∃ w f, chainB (pre :: loops[w₁] … loops[w_k] :: finals[f]) ⊤ ρ₀ q₀`, the chain of the abstract
meanings of the blocks (`FOND.DB.chainB`).
-/

namespace FOND

namespace DB

open Problem

/-- The phases of a block. -/
def blockPhases (ops : List Op) : List (List FActDesc) := ops.flatMap opPhases

/-- The initial state as a list. -/
def initList (V : List ℕ) (ρ₀ : ℕ → Bool) (q₀ : ℕ) : List ℕ := V.map (fun v => lit v (ρ₀ v)) ++ [qF q₀]

theorem initList_eq (V : List ℕ) (ρ₀ : ℕ → Bool) (q₀ : ℕ) :
    {x | x ∈ initList V ρ₀ q₀} = enc V ρ₀ q₀ := by
  ext f; simp [initList, enc, eq_comm]

/-- **The chain of blocks**, abstractly. -/
def chainB : List (List Op) → ((ℕ → Bool) → ℕ → Prop) → (ℕ → Bool) → ℕ → Prop
  | [], K => K
  | ops :: L, K => blockSem ops (chainB L K)

theorem chainP_ops {V : List ℕ} (K : Set ℕ → Prop) : ∀ (L : List (List Op)),
    (∀ ops ∈ L, ∀ op ∈ ops, OpWF V op) → ∀ ρ q,
    (chainP (L.map blockPhases) K (enc V ρ q) ↔ chainB L (fun ρ q => K (enc V ρ q)) ρ q)
  | [], _, ρ, q => Iff.rfl
  | ops :: L, h, ρ, q => by
    simp only [List.map_cons, chainP, chainB, blockPhases]
    have ih := chainP_ops K L (fun o ho => h o (by simp [ho]))
    rw [phasesWin_block ops (h ops (by simp))]
    have : (fun ρ q => chainP (L.map blockPhases) K (enc V ρ q)) =
        chainB L (fun ρ q => K (enc V ρ q)) := funext fun ρ => funext fun q => propext (ih ρ q)
    rw [this]

theorem opPhases_effs (op : Op) : ∀ ph ∈ opPhases op, ∀ a ∈ ph, a.2.2.2 ≠ [] := by
  cases op with
  | check Φ =>
    intro ph hph a ha
    simp only [opPhases, List.mem_flatMap, clausePhases, List.mem_append, List.mem_map,
      List.mem_cons, List.not_mem_nil, or_false] at hph
    obtain ⟨C, -, (⟨v, -, rfl⟩ | rfl | rfl)⟩ := hph
    · simp only [hcopy, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> simp [cpA]
    · simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ⟨l, -, rfl⟩ | rfl | rfl <;> simp [chkA, finA, clrA]
    · simp only [List.mem_singleton] at ha; subst ha; simp [rstA]
  | _ =>
    intro ph hph a ha
    simp only [opPhases, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hph
    subst hph
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    first
    | (subst ha; simp [setA, natA, cpA, updA])
    | (rcases ha with rfl | rfl <;> simp [setA, natA, cpA, updA])

theorem blockPhases_effs (ops : List Op) : ∀ ph ∈ blockPhases ops, ∀ a ∈ ph, a.2.2.2 ≠ [] := by
  intro ph hph
  obtain ⟨op, -, hph⟩ := List.mem_flatMap.1 hph
  exact opPhases_effs op ph hph

/-- **The description of a regular problem from register programs.** -/
def opDesc (V : List ℕ) (ρ₀ : ℕ → Bool) (q₀ : ℕ) (pre : List Op) (loops finals : List (List Op)) :
    FProbDesc :=
  mkDesc (initList V ρ₀ q₀) (blockPhases pre) (loops.map blockPhases) (finals.map blockPhases)

theorem effsNe_opDesc (pre : List Op) (loops finals : List (List Op)) :
    EffsNe (mlist (blockPhases pre) (loops.map blockPhases) (finals.map blockPhases)) := by
  intro e he ph hph a ha
  simp only [mlist, List.mem_cons, List.mem_append, List.mem_map] at he
  rcases he with rfl | ⟨_, ⟨ops, -, rfl⟩, rfl⟩ | ⟨_, ⟨ops, -, rfl⟩, rfl⟩
  · exact blockPhases_effs pre ph hph a ha
  · exact blockPhases_effs ops ph hph a ha
  · exact blockPhases_effs ops ph hph a ha

theorem opDesc_valid (V : List ℕ) (ρ₀ : ℕ → Bool) (q₀ : ℕ) (pre : List Op)
    (loops finals : List (List Op)) : (opDesc V ρ₀ q₀ pre loops finals).Valid :=
  mkDesc_valid (effsNe_opDesc pre loops finals)

/-- **Strong OD plan existence of a register program problem.** -/
theorem opDesc_strongOD_iff {V : List ℕ} {ρ₀ : ℕ → Bool} {q₀ : ℕ} {pre : List Op}
    {loops finals : List (List Op)} (hwf : ∀ ops ∈ pre :: (loops ++ finals), ∀ op ∈ ops, OpWF V op) :
    (opDesc V ρ₀ q₀ pre loops finals).toProblem.StrongODSolvable ↔
      ∃ (ws : List ℕ) (f : ℕ), (∀ w ∈ ws, w < loops.length) ∧ f < finals.length ∧
        chainB (pre :: (ws.map loops.getI ++ [finals.getI f])) (fun _ _ => True) ρ₀ q₀ := by
  rw [opDesc, mkDesc_strongOD_iff (effsNe_opDesc pre loops finals), initList_eq]
  simp only [List.length_map]
  refine exists_congr fun ws => exists_congr fun f => and_congr_right fun hws =>
    and_congr_right fun hf => ?_
  have hgetL : ∀ w ∈ ws, (loops.map blockPhases).getI w = blockPhases (loops.getI w) := by
    intro w hw
    rw [List.getI_eq_getElem _ (by simpa using hws w hw), List.getI_eq_getElem _ (hws w hw)]
    simp
  have hgetF : (finals.map blockPhases).getI f = blockPhases (finals.getI f) := by
    rw [List.getI_eq_getElem _ (by simpa using hf), List.getI_eq_getElem _ hf]; simp
  have hL : pre.flatMap opPhases :: ((ws.map (loops.map blockPhases).getI) ++
      [(finals.map blockPhases).getI f]) =
      (pre :: (ws.map loops.getI ++ [finals.getI f])).map blockPhases := by
    simp only [List.map_cons, List.map_append, List.map_map, List.map_nil, blockPhases]
    congr 1
    · congr 1
      · exact List.map_congr_left fun w hw => by simpa [blockPhases] using hgetL w hw
      · simpa [blockPhases] using hgetF
  rw [show blockPhases pre = pre.flatMap opPhases from rfl, hL,
    chainP_ops (fun _ => True) _ ?_ ρ₀ q₀]
  intro ops hops op hop
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hops
  rcases hops with rfl | (⟨w, hw, rfl⟩ | h)
  · exact hwf _ (by simp) op hop
  · refine hwf _ ?_ op hop
    rw [List.getI_eq_getElem _ (hws w hw)]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.getElem_mem _))
  · obtain rfl : ops = finals.getI f := by simpa using h
    refine hwf _ ?_ op hop
    rw [List.getI_eq_getElem _ hf]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.getElem_mem _))

end DB

end FOND
