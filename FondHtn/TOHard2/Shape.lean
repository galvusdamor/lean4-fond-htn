import FondHtn.TOHard2.Desc
/-!
# The shape of the grammar

* `FOND.TOHard2.gram_good` — the grammar is well formed (instruction names determine the
  instructions, `FOND.TOHard2.insOf`; all alternatives are well formed and have an effect);
* membership of the instructions used by the programs (`mem_insL_*`);
* the methods of each kind of nonterminal (`meth_root`, `meth_K`, `meth_sub`, `meth_bb`,
  `meth_ch`, `meth_lam` and the converse membership lemmas).
-/

set_option linter.unusedSimpArgs false

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

variable (P : Par)

/-! ## Instructions -/

/-- The instruction of a name. -/
def insOf (n : ℕ) : List ASpec :=
  let t := n.unpair.1
  let p := n.unpair.2
  if t = 0 then setEQ.2 else if t = 1 then (cmpI p).2 else if t = 2 then (incI P.b).2
  else if t = 3 then finI.2 else if t = 4 then (f01I (decide (p = 1))).2
  else if t = 5 then (f10I (decide (p = 1))).2 else if t = 6 then (bitI (decide (p = 1))).2
  else if t = 7 then (ceAI P.b p (P.cs.getI p)).2
  else if t = 8 then (ceBI P.b p.unpair.1 p.unpair.2 ((P.cs.getI p.unpair.1).getI p.unpair.2)).2
  else if t = 9 then cwAI.2
  else if t = 10 then (cwBI P.b p.unpair.1 p.unpair.2 ((P.cs.getI p.unpair.1).getI p.unpair.2)).2
  else if t = 11 then (cvI P.b p (P.cs.getI p)).2 else if t = 12 then (pickChkI p).2
  else if t = 13 then clrTBI.2 else if t = 14 then guessIBI.2 else if t = 15 then pick3I.2
  else if t = 16 then pickLCI.2 else if t = 17 then pickCRI.2 else if t = 18 then (assertMI p).2
  else if t = 19 then (assertIBI (decide (p = 1))).2 else assertTBI.2

theorem insOf_iN (t p : ℕ) : insOf P (iN t p) =
    if t = 0 then setEQ.2 else if t = 1 then (cmpI p).2 else if t = 2 then (incI P.b).2
    else if t = 3 then finI.2 else if t = 4 then (f01I (decide (p = 1))).2
    else if t = 5 then (f10I (decide (p = 1))).2 else if t = 6 then (bitI (decide (p = 1))).2
    else if t = 7 then (ceAI P.b p (P.cs.getI p)).2
    else if t = 8 then (ceBI P.b p.unpair.1 p.unpair.2 ((P.cs.getI p.unpair.1).getI p.unpair.2)).2
    else if t = 9 then cwAI.2
    else if t = 10 then (cwBI P.b p.unpair.1 p.unpair.2 ((P.cs.getI p.unpair.1).getI p.unpair.2)).2
    else if t = 11 then (cvI P.b p (P.cs.getI p)).2 else if t = 12 then (pickChkI p).2
    else if t = 13 then clrTBI.2 else if t = 14 then guessIBI.2 else if t = 15 then pick3I.2
    else if t = 16 then pickLCI.2 else if t = 17 then pickCRI.2 else if t = 18 then (assertMI p).2
    else if t = 19 then (assertIBI (decide (p = 1))).2 else assertTBI.2 := by
  simp only [insOf, iN, Nat.unpair_pair]

theorem actP_fun (k : ℕ) : ∀ q ∈ actP P.b P.cs (.ce k) ++ actP P.b P.cs (.cw k) ++ actP P.b P.cs (.cv k),
    q.2 = insOf P q.1 := by
  intro q hq
  simp only [actP, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hq
  rcases hq with ((rfl | ⟨j, -, rfl⟩) | (rfl | ⟨j, -, rfl⟩)) | rfl <;>
    simp [insOf_iN, ceAI, ceBI, cwAI, cwBI, cvI, Nat.unpair_pair]

theorem insRaw_fun : ∀ q ∈ insRaw P, q.2 = insOf P q.1 := by
  intro q hq
  simp only [insRaw, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.mem_flatMap, pickChks] at hq
  rcases hq with ((h | ⟨r, -, rfl⟩) | ⟨r, -, rfl⟩) | ⟨k, -, hk⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [insOf_iN, setEQ, incI, finI, f01I, f10I, bitI, cwAI, clrTBI, guessIBI, pick3I, pickLCI,
        pickCRI, pickMI, assertMI, assertIBI, assertTBI]
  · simp [insOf_iN, cmpI]
  · simp [insOf_iN, pickChkI]
  · exact actP_fun P k q (by simp only [List.mem_append] at hk ⊢; tauto)

theorem goodSpec_tst (alts : List (List ℕ × List ℕ)) : ∀ a ∈ tst alts, a.WF ∧ a.effs ≠ [] := by
  intro a ha
  obtain ⟨pn, -, rfl⟩ := List.mem_map.1 ha
  simp [ASpec.WF, ASpec.cnew, ASpec.effs, noeff]

theorem goodSpec_of {ins : List ASpec} (h : ∀ a ∈ ins, a.2.2.2.2 = [] ∧ a.2.2.1 ≠ []) :
    ∀ a ∈ ins, a.WF ∧ a.effs ≠ [] := fun a ha =>
  ⟨⟨by simp [ASpec.cnew, (h a ha).1], fun h' => absurd (h a ha).1 h'⟩, (h a ha).2⟩

theorem insRaw_spec : ∀ q ∈ insRaw P, ∀ a ∈ q.2, a.WF ∧ a.effs ≠ [] := by
  intro q hq
  simp only [insRaw, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, List.mem_flatMap, pickChks] at hq
  rcases hq with ((h | ⟨r, -, rfl⟩) | ⟨r, -, rfl⟩) | ⟨k, -, hk⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact goodSpec_tst _
      | (intro a ha; simp only [incI, List.mem_append, List.mem_map, List.mem_range,
          List.mem_singleton] at ha
         rcases ha with ⟨j, -, rfl⟩ | rfl <;> simp [ASpec.WF, ASpec.cnew, ASpec.effs])
      | (apply goodSpec_of
         simp [setEQ, incI, finI, f01I, f10I, bitI, cwAI, clrTBI, guessIBI, pick3I, pickLCI,
          pickCRI, pickMI, pickI, guessI, assertMI, assertIBI, assertTBI, noeff, tst])
  · apply goodSpec_of; simp [cmpI, noeff]
  · apply goodSpec_of; simp [pickChkI]
  · simp only [actP, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hk
    rcases hk with ((rfl | ⟨j, -, rfl⟩) | (rfl | ⟨j, -, rfl⟩)) | rfl <;> exact goodSpec_tst _

theorem gram_insL : (gram P).insL = @List.dedup _ decEqInsP (insRaw P) := by simp only [gram]

theorem gram_methL : (gram P).methL = meths P := by simp only [gram]

theorem mem_insL {q : ℕ × List ASpec} : q ∈ (gram P).insL ↔ q ∈ insRaw P := by
  rw [gram_insL]; exact @List.mem_dedup _ decEqInsP _ _

/-- **The grammar is well formed.** -/
theorem gram_good : (gram P).Good where
  nodup := by
    unfold Gram.InsNodup
    rw [gram_insL]
    refine (@List.nodup_dedup _ decEqInsP _).map_on fun x hx y hy hxy => Prod.ext hxy ?_
    rw [insRaw_fun P x ((@List.mem_dedup _ decEqInsP _ _).1 hx),
      insRaw_fun P y ((@List.mem_dedup _ decEqInsP _ _).1 hy), hxy]
  spec := fun q hq => insRaw_spec P q ((mem_insL P).1 hq)

/-- The constants of an atomic type are declared. -/
def AT.Ok (n : ℕ) : AT → Prop
  | .ce k => k < n
  | .cw k => k < n
  | .cv k => k < n
  | _ => True

theorem actP_mem {a : AT} (ha : a.Ok P.cs.length) : ∀ q ∈ actP P.b P.cs a, q ∈ (gram P).insL := by
  intro q hq
  rw [mem_insL]
  cases a with
  | id => simp [actP] at hq
  | f01 rg => simp [actP] at hq; subst hq; cases rg <;> simp [insRaw]
  | f10 rg => simp [actP] at hq; subst hq; cases rg <;> simp [insRaw]
  | bit β => simp [actP] at hq; subst hq; cases β <;> simp [insRaw]
  | ce k => exact List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 ha, by simp [hq]⟩)
  | cw k => exact List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 ha, by simp [hq]⟩)
  | cv k => exact List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 ha, by simp [hq]⟩)

theorem block_mem {a : AT} (ha : a.Ok P.cs.length) : ∀ q ∈ block P.b P.cs a, q ∈ (gram P).insL := by
  intro q hq
  simp only [block, cmps, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hq
  rcases hq with ((rfl | ⟨r, hr, rfl⟩) | h) | rfl
  · rw [mem_insL]; simp [insRaw]
  · rw [mem_insL]; simp only [insRaw, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨r, hr, rfl⟩))
  · exact actP_mem P ha q h
  · rw [mem_insL]; simp [insRaw]

theorem blocks_mem {as : List AT} (ha : ∀ a ∈ as, a.Ok P.cs.length) :
    ∀ q ∈ blocks P.b P.cs as, q ∈ (gram P).insL := by
  intro q hq
  obtain ⟨a, ha', hq⟩ := List.mem_flatMap.1 hq
  exact block_mem P (ha a ha') q hq

theorem chain_mem {as : List AT} (ha : ∀ a ∈ as, a.Ok P.cs.length) :
    ∀ q ∈ chain P.b P.cs as, q ∈ (gram P).insL := by
  intro q hq
  rcases List.mem_append.1 hq with hq | hq
  · exact blocks_mem P ha q hq
  · simp at hq; subst hq; rw [mem_insL]; simp [insRaw]

theorem pickChks_mem : ∀ q ∈ pickChks P, q ∈ (gram P).insL := by
  intro q hq; rw [mem_insL]; simp only [insRaw, List.mem_append]; exact Or.inl (Or.inr hq)

theorem insRaw_mem_of_mem {q : ℕ × List ASpec}
    (h : q ∈ [setEQ, incI P.b, finI, f01I true, f01I false, f10I true, f10I false, bitI false,
      bitI true, cwAI, clrTBI, guessIBI, pick3I, pickLCI, pickCRI, assertMI 0, assertMI 1, assertMI 2,
      assertIBI false, assertIBI true, assertTBI]) : q ∈ (gram P).insL := by
  rw [mem_insL]; simp only [insRaw, List.mem_append]; exact Or.inl (Or.inl (Or.inl h))

/-! ## Methods -/

/-- The tag of a nonterminal name. -/
def tag (n : ℕ) : ℕ := n.unpair.1

@[simp] theorem tag_kN (t p : ℕ) : tag (kN t p) = t := by simp [tag, kN]

theorem mem_lamMeths {A : Comp} {y n : ℕ} {bs : List (Bool × ℕ)} :
    (n, bs) ∈ lamMeths P A y ↔ ∃ t ∈ A.aut.trans, n = lamN A t.2.2 y ∧
      (bs = (true, lamN A t.1 y) :: syms (block P.b P.cs t.2.1) ∨
        (t.1 = A.aut.init ∧ bs = (true, y) :: syms (block P.b P.cs t.2.1))) := by
  simp only [lamMeths, List.mem_flatMap, List.mem_cons, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, ⟨h1, h2⟩ | h⟩
    · exact ⟨t, ht, h1, Or.inl h2⟩
    · split_ifs at h with h0
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        exact ⟨t, ht, h.1, Or.inr ⟨h0, h.2⟩⟩
      · simp at h
  · rintro ⟨t, ht, h1, h2 | ⟨h0, h2⟩⟩
    · exact ⟨t, ht, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨t, ht, Or.inr (by rw [if_pos h0]; simp [h1, h2])⟩

theorem head_chMeths {A : Comp} {y : ℕ} {q : ℕ × List (Bool × ℕ)} (hq : q ∈ chMeths P A y) :
    (q = (chN A y, chBody A y)) ∨ (q ∈ lamMeths P A y ∧ ∃ σ, q.1 = lamN A σ y) := by
  rcases List.mem_cons.1 hq with rfl | hq
  · exact Or.inl rfl
  · refine Or.inr ⟨hq, ?_⟩
    obtain ⟨t, -, h, -⟩ := (mem_lamMeths P (n := q.1) (bs := q.2)).1 hq
    exact ⟨_, h⟩

theorem allChMeths_cases {q : ℕ × List (Bool × ℕ)} (hq : q ∈ allChMeths P) :
    ∃ A y, q ∈ chMeths P A y := by
  simp only [allChMeths, modeChMeths, List.mem_append, List.mem_flatMap] at hq
  rcases hq with (⟨x, -, (((((h | h) | h) | h) | h) | h)⟩ | ((h | h) | h) | h) | ⟨a, -, h | h⟩ <;>
    exact ⟨_, _, h⟩

theorem tag_allChMeths {q : ℕ × List (Bool × ℕ)} (hq : q ∈ allChMeths P) :
    tag q.1 = 4 ∨ tag q.1 = 5 := by
  obtain ⟨A, y, h⟩ := allChMeths_cases P hq
  rcases head_chMeths P h with rfl | ⟨-, σ, h⟩
  · simp [chN]
  · rw [h]; simp [lamN]

theorem tag_meths {q : ℕ × List (Bool × ℕ)} (hq : q ∈ meths P) :
    (tag q.1 = 0 ∧ q ∈ rootMeths P) ∨ (tag q.1 = 1 ∧ q ∈ kMeths P) ∨ (tag q.1 = 2 ∧ q ∈ subMeths P) ∨
      (q = (bbN, bbBody P)) ∨ (q ∈ allChMeths P ∧ (tag q.1 = 4 ∨ tag q.1 = 5)) := by
  simp only [meths, List.mem_append, List.mem_singleton] at hq
  rcases hq with (((h | h) | h) | h) | h
  · left; refine ⟨?_, h⟩
    simp only [rootMeths, List.mem_map] at h; obtain ⟨a, -, rfl⟩ := h; simp [rootN]
  · right; left; refine ⟨?_, h⟩
    simp only [kMeths, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at h
    rcases h with (((⟨j, -, rfl⟩ | ⟨j, -, rfl⟩) | ⟨j, -, rfl⟩) | ⟨c, -, rfl⟩) | rfl | rfl <;> simp [KN]
  · right; right; left; refine ⟨?_, h⟩
    simp only [subMeths, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at h
    rcases h with (⟨j, -, rfl | rfl | rfl⟩ | ⟨j, -, rfl | rfl⟩) | ⟨j, -, rfl | rfl⟩ <;> simp [subN]
  · right; right; right; left; exact h
  · right; right; right; right; exact ⟨h, tag_allChMeths P h⟩

/-- **The methods of the root.** -/
theorem meth_root {bs : List (Bool × ℕ)} (h : (rootN, bs) ∈ meths P) :
    ∃ a ∈ P.acc, bs = [(true, chN .cpy (chN .bits (KN a))), (false, assertTBI.1)] := by
  rcases tag_meths P h with ⟨-, h⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h | ⟨-, ht⟩
  · simp only [rootMeths, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨a, ha, -, rfl⟩ := h; exact ⟨a, ha, rfl⟩
  · simp [rootN] at ht
  · simp [rootN] at ht
  · simp [rootN, bbN] at h
  · simp [rootN] at ht

theorem mem_root {a : ℕ} (ha : a ∈ P.acc) :
    (rootN, [(true, chN .cpy (chN .bits (KN a))), (false, assertTBI.1)]) ∈ (gram P).methL := by
  rw [gram_methL]; simp only [meths, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map.2 ⟨a, ha, rfl⟩))))

/-- **The methods of a claim.** -/
theorem meth_K {a : ℕ} {bs : List (Bool × ℕ)} (h : (KN a, bs) ∈ meths P) :
    (∃ j < P.mid.length, (P.mid.getI j).1 = a ∧ bs = [(false, pick3I.1), (true, subN 0 j)]) ∨
    (∃ j < P.lft.length, (P.lft.getI j).1 = a ∧ bs = [(false, pickCRI.1), (true, subN 1 j)]) ∨
    (∃ j < P.rgt.length, (P.rgt.getI j).1 = a ∧ bs = [(false, pickLCI.1), (true, subN 2 j)]) ∨
    (∃ c < P.baseU.length, P.baseU.getI c = a ∧ bs = prefBody P c) ∨
    (a = P.codeTrue ∧ bs = [(true, chN (.cmp 0 true) (chN (.cmp 1 false) bbN))]) ∨
    (a = P.codeNone ∧ bs = [(true, chN (.cmp 1 true) (chN .cpy bbN))]) := by
  rcases tag_meths P h with ⟨ht, -⟩ | ⟨-, h⟩ | ⟨ht, -⟩ | h | ⟨-, ht⟩
  · simp [KN] at ht
  · simp only [kMeths, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      Prod.mk.injEq, KN_inj, List.not_mem_nil, or_false] at h
    rcases h with (((⟨j, hj, h1, h2⟩ | ⟨j, hj, h1, h2⟩) | ⟨j, hj, h1, h2⟩) | ⟨c, hc, h1, h2⟩) |
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨j, hj, h1, h2.symm⟩
    · exact Or.inr (Or.inl ⟨j, hj, h1, h2.symm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, hj, h1, h2.symm⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, h1, h2.symm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))
  · simp [KN] at ht
  · simp [KN, bbN] at h
  · simp [KN] at ht

theorem mem_K_of_mem_kMeths {q : ℕ × List (Bool × ℕ)} (h : q ∈ kMeths P) : q ∈ (gram P).methL := by
  rw [gram_methL]; simp only [meths, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr h)))

/-- **The methods of a challenge nonterminal.** -/
theorem meth_sub {k j : ℕ} {bs : List (Bool × ℕ)} (h : (subN k j, bs) ∈ meths P) :
    (k = 0 ∧ j < P.mid.length ∧ (bs = modeBody 0 (P.mid.getI j).2.1 ∨ bs = modeBody 1 (P.mid.getI j).2.2.1 ∨
      bs = modeBody 2 (P.mid.getI j).2.2.2)) ∨
    (k = 1 ∧ j < P.lft.length ∧ (bs = modeBody 1 (P.lft.getI j).2.1 ++ [(false, (assertIBI false).1)] ∨
      bs = modeBody 2 (P.lft.getI j).2.2 ++ [(false, (assertIBI false).1)])) ∨
    (k = 2 ∧ j < P.rgt.length ∧ (bs = modeBody 0 (P.rgt.getI j).2.1 ++ [(false, (assertIBI true).1)] ∨
      bs = modeBody 1 (P.rgt.getI j).2.2 ++ [(false, (assertIBI true).1)])) := by
  rcases tag_meths P h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, h⟩ | h | ⟨-, ht⟩
  · simp [subN] at ht
  · simp [subN] at ht
  · simp only [subMeths, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      Prod.mk.injEq, subN_inj, List.not_mem_nil, or_false] at h
    rcases h with (⟨j', hj, ⟨⟨rfl, rfl⟩, h⟩ | ⟨⟨rfl, rfl⟩, h⟩ | ⟨⟨rfl, rfl⟩, h⟩⟩ |
      ⟨j', hj, ⟨⟨rfl, rfl⟩, h⟩ | ⟨⟨rfl, rfl⟩, h⟩⟩) | ⟨j', hj, ⟨⟨rfl, rfl⟩, h⟩ | ⟨⟨rfl, rfl⟩, h⟩⟩
    · exact Or.inl ⟨rfl, hj, Or.inl h⟩
    · exact Or.inl ⟨rfl, hj, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨rfl, hj, Or.inr (Or.inr h)⟩
    · exact Or.inr (Or.inl ⟨rfl, hj, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨rfl, hj, Or.inr h⟩)
    · exact Or.inr (Or.inr ⟨rfl, hj, Or.inl h⟩)
    · exact Or.inr (Or.inr ⟨rfl, hj, Or.inr h⟩)
  · simp [subN, bbN] at h
  · simp [subN] at ht

theorem mem_sub_of_mem {q : ℕ × List (Bool × ℕ)} (h : q ∈ subMeths P) : q ∈ (gram P).methL := by
  rw [gram_methL]; simp only [meths, List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))

theorem meth_bb {bs : List (Bool × ℕ)} (h : (bbN, bs) ∈ meths P) : bs = bbBody P := by
  rcases tag_meths P h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h | ⟨-, ht⟩
  · simp [bbN] at ht
  · simp [bbN] at ht
  · simp [bbN] at ht
  · simp only [Prod.mk.injEq] at h; exact h.2
  · simp [bbN] at ht

theorem mem_bb : (bbN, bbBody P) ∈ (gram P).methL := by
  rw [gram_methL]; simp only [meths, List.mem_append]
  exact Or.inl (Or.inr (List.mem_singleton_self _))

theorem meth_ch {A : Comp} {y : ℕ} {bs : List (Bool × ℕ)} (h : (chN A y, bs) ∈ meths P) :
    bs = chBody A y := by
  rcases tag_meths P h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h | ⟨h, -⟩
  · simp [chN] at ht
  · simp [chN] at ht
  · simp [chN] at ht
  · simp [chN, bbN] at h
  · obtain ⟨A', y', h'⟩ := allChMeths_cases P h
    rcases head_chMeths P h' with h'' | ⟨-, σ, h''⟩
    · simp only [Prod.mk.injEq, chN_inj] at h''
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h''; rfl
    · simp [chN, lamN] at h''

theorem meth_lam {A : Comp} {σ y : ℕ} {bs : List (Bool × ℕ)} (h : (lamN A σ y, bs) ∈ meths P) :
    (lamN A σ y, bs) ∈ lamMeths P A y := by
  rcases tag_meths P h with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h | ⟨h, -⟩
  · simp [lamN] at ht
  · simp [lamN] at ht
  · simp [lamN] at ht
  · simp [lamN, bbN] at h
  · obtain ⟨A', y', h'⟩ := allChMeths_cases P h
    rcases head_chMeths P h' with h'' | ⟨h'', σ', h3⟩
    · simp [chN, lamN] at h''
    · simp only [lamN_inj] at h3
      obtain ⟨rfl, -, rfl⟩ := h3
      exact h''

/-- Chain methods present in the grammar. -/
def ChIn (A : Comp) (y : ℕ) : Prop := ∀ q ∈ chMeths P A y, q ∈ (gram P).methL

theorem chIn_of_sub {A : Comp} {y : ℕ} (h : chMeths P A y ⊆ allChMeths P) : ChIn P A y := by
  intro q hq
  rw [gram_methL]; simp only [meths, List.mem_append]
  exact Or.inr (h hq)

/-- **The left recursion of a chain**, soundness direction. -/
theorem lam_sound {A : Comp} {y : ℕ} (σ : ℕ) (bs : List (Bool × ℕ))
    (h : (lamN A σ y, bs) ∈ (gram P).methL) : ∃ σ' a, (σ', a, σ) ∈ A.aut.trans ∧
      (bs = (true, lamN A σ' y) :: syms (block P.b P.cs a) ∨
        (σ' = A.aut.init ∧ bs = (true, y) :: syms (block P.b P.cs a))) := by
  rw [gram_methL] at h
  obtain ⟨t, ht, h1, h2⟩ := (mem_lamMeths P).1 (meth_lam P h)
  obtain ⟨σ', a, σ''⟩ := t
  simp only [lamN_inj, true_and] at h1
  obtain ⟨rfl, -⟩ := h1
  exact ⟨σ', a, ht, h2⟩

/-- **The left recursion of a chain**, completeness direction. -/
theorem lam_complete {A : Comp} {y : ℕ} (hin : ChIn P A y) (σ : ℕ) (bs : List (Bool × ℕ))
    (h : ∃ σ' a, (σ', a, σ) ∈ A.aut.trans ∧
      (bs = (true, lamN A σ' y) :: syms (block P.b P.cs a) ∨
        (σ' = A.aut.init ∧ bs = (true, y) :: syms (block P.b P.cs a)))) :
    (lamN A σ y, bs) ∈ (gram P).methL := by
  obtain ⟨σ', a, ht, h⟩ := h
  exact hin _ (List.mem_cons_of_mem _ ((mem_lamMeths P).2 ⟨(σ', a, σ), ht, rfl, h⟩))

end TOHard2

end FOND
