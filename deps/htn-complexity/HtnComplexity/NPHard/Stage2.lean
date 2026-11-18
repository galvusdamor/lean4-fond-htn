import HtnComplexity.NPHard.Tokens
import HtnComplexity.NPHard.CobList
/-!
# The numerical stage in polynomial time

The stage that maps the token code of a formula (`cnfCode n φ = unl (n :: toks φ)`) to the code
of its explicit numerical instance (`numCode`: the target sum, the number of groups and the
numbers `numsOf n φ`) is a function of Cobham's class (`cobham_stage2`), and computes the right
thing on codes of formulas (`stage2_cnfCode`).
-/

namespace HTN.NPHard

open HTN.PTime HTN.PTime.CobhamTM Merge

/-! ### Reading a list of numbers -/

/-- The list of numbers written in a string (leading `true`s are ignored). -/
def parseUnl : List Bool → List ℕ
  | [] => []
  | true :: x => parseUnl x
  | false :: x => (x.takeWhile id).length :: parseUnl x

theorem parseUnl_un_append (n : ℕ) (y : List Bool) : parseUnl (un n ++ y) = parseUnl y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [un, List.replicate_succ, List.cons_append] at ih ⊢; simp [parseUnl, ih]

@[simp] theorem parseUnl_unl (l : List ℕ) : parseUnl (unl l) = l := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    rw [unl_cons, parseUnl, takeWhile_un_append, length_un, parseUnl_un_append, ih]

theorem takeWhile_id_eq_un (x : List Bool) : x.takeWhile id = un (x.takeWhile id).length := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b
    · simp [un]
    · rw [List.takeWhile_cons_of_pos (by rfl), List.length_cons, un, List.replicate_succ, ← un, ← ih]

theorem unl_parseUnl (x : List Bool) : unl (parseUnl x) = x.dropWhile id := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b
    · rw [parseUnl, unl_cons, ih, ← takeWhile_id_eq_un, List.takeWhile_append_dropWhile]
      rfl
    · rw [parseUnl, ih]; rfl

theorem flatMap_not_not (x : List Bool) :
    (x.flatMap fun b => [!b]).flatMap (fun b => [!b]) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [ih]

theorem cobham_dropTrues {a : Fn} (ha : Cobham a) : Cobham fun args => (a args).dropWhile id := by
  have h := cobham_flatMapBits (fun b => [!b])
    (cobham_dropFalses (cobham_flatMapBits (fun b => [!b]) ha))
  refine h.of_fun_eq fun args => ?_
  generalize a args = x
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b
    · simp [flatMap_not_not]
    · simpa using ih

theorem cobList_parse {a : Fn} (ha : Cobham a) : CobList fun args => parseUnl (a args) :=
  (cobham_dropTrues ha).of_fun_eq fun args => (unl_parseUnl _).symm

theorem cobList_tail {L : Args → List ℕ} (hL : CobList L) : CobList fun args => (L args).tail := by
  refine (cobham_dropTrues (cobham_tail' hL)).of_fun_eq fun args => ?_
  show _ = unl (L args).tail
  rcases L args with _ | ⟨n, l⟩
  · rfl
  · rw [unl_cons, List.tail_cons, List.dropWhile_append_of_pos]
    · rcases l with _ | ⟨k, l⟩ <;> rfl
    · intro b hb; simp only [un, List.mem_replicate] at hb; simp [hb.2]

/-! ### Loops in argument form -/

theorem cobList_loop {N : Args → ℕ} (hN : CobN N) {F : ℕ → Args → List ℕ}
    (hF : CobList fun args => F (args.getD 0 []).length args.tail) :
    CobList fun args => (List.range (N args)).flatMap fun i => F i args :=
  (cobList_forRange hN hF).of_eq fun args => by simp

theorem CobN.dropN {f : Args → ℕ} (hf : CobN f) (d : ℕ) : CobN fun args => f (args.drop d) :=
  CobhamTM.cobham_dropArgs hf d

theorem CobList.dropN {L : Args → List ℕ} (hL : CobList L) (d : ℕ) :
    CobList fun args => L (args.drop d) :=
  CobhamTM.cobham_dropArgs hL d

/-- **A loop over the literals of a computed token list.** -/
theorem cobList_tokLoop {T : Args → List ℕ} (hT : CobList T)
    {G : ℕ → ℕ × Bool → Bool → Args → List ℕ}
    (hG : CobList fun args => G (args.getD 0 []).length (decLit (args.getD 1 []).length)
      (decide ((args.getD 2 []).length = 0)) (args.drop 4)) :
    CobList fun args => tokLoop (fun j l b => G j l b args) (T args) 0 := by
  unfold tokLoop
  refine cobList_loop (cobN_length hT) ?_
  have hTi : CobN fun args => (T args.tail).getD (args.getD 0 []).length 0 :=
    cobN_getD hT.drop1 (cobN_arg 0)
  have hTi1 : CobN fun args => (T args.tail).getD ((args.getD 0 []).length + 1) 0 :=
    cobN_getD hT.drop1 (cobN_add (cobN_arg 0) (cobN_const 1))
  have hzb : CobN fun args => zerosBefore (T args.tail) (args.getD 0 []).length := by
    unfold zerosBefore
    refine (cobN_count (cobN_arg 0) (p := fun args =>
      decide ((T (args.drop 2)).getD (args.getD 0 []).length 0 = 0))
      (cobB_eq (cobN_getD (hT.dropN 2) (cobN_arg 0)) (cobN_const 0))).of_eq fun args => ?_
    simp [List.drop_one]
  have hb := CobhamTM.cobham_prepend hG [fun args => un (0 + zerosBefore (T args.tail)
      (args.getD 0 []).length - 1), fun args => un ((T args.tail).getD (args.getD 0 []).length 0),
      fun args => un ((T args.tail).getD ((args.getD 0 []).length + 1) 0)] (by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl
    · exact cobN_sub (cobN_add (cobN_const 0) hzb) (cobN_const 1)
    · exact hTi
    · exact hTi1)
  refine (cobList_ite (cobB_eq hTi (cobN_const 0)) cobList_nil hb).of_eq fun args => ?_
  simp [List.drop_one]

theorem cobList_loop2 {N M : Args → ℕ} (hN : CobN N) (hM : CobN M) {G : ℕ → ℕ → Args → List ℕ}
    (hG : CobList fun args => G (args.getD 1 []).length (args.getD 0 []).length (args.drop 2)) :
    CobList fun args => (List.range (N args)).flatMap fun i =>
      (List.range (M args)).flatMap fun j => G i j args :=
  cobList_loop hN (cobList_loop hM.drop1 (hG.of_eq fun args => by
    rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩ <;> rfl))

theorem cobList_loop3 {N M P : Args → ℕ} (hN : CobN N) (hM : CobN M) (hP : CobN P)
    {G : ℕ → ℕ → ℕ → Args → List ℕ}
    (hG : CobList fun args => G (args.getD 2 []).length (args.getD 1 []).length
      (args.getD 0 []).length (args.drop 3)) :
    CobList fun args => (List.range (N args)).flatMap fun i =>
      (List.range (M args)).flatMap fun j => (List.range (P args)).flatMap fun k => G i j k args :=
  cobList_loop hN (cobList_loop2 hM.drop1 hP.drop1 (hG.of_eq fun args => by
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, args⟩⟩⟩ <;> rfl))

/-! ### Numbers of items -/

theorem cobN_hor {r a0 a1 a2 a3 a4 : Args → ℕ} (hr : CobN r) (h0 : CobN a0) (h1 : CobN a1)
    (h2 : CobN a2) (h3 : CobN a3) (h4 : CobN a4) :
    CobN fun args => hor (r args) (a0 args) (a1 args) (a2 args) (a3 args) (a4 args) :=
  cobN_add h0 (cobN_mul hr (cobN_add h1 (cobN_mul hr (cobN_add h2 (cobN_mul hr
    (cobN_add h3 (cobN_mul hr h4)))))))

theorem cobN_radix {q : Args → ℕ} (hq : CobN q) : CobN fun args => radix (q args) :=
  cobN_add (cobN_mul (cobN_const 4) hq) (cobN_const 100)

theorem cobN_valTrip {q a b c : Args → ℕ} (hq : CobN q) (ha : CobN a) (hb : CobN b)
    (hc : CobN c) : CobN fun args => Item.val (q args) (Item.trip (a args, b args, c args)) :=
  cobN_hor (cobN_radix hq) (cobN_const 8) (cobN_sub hq ha) (cobN_sub hq hb) (cobN_sub hq hc)
    (cobN_const 20)

theorem cobN_valW (d : Bool) {q e : Args → ℕ} (hq : CobN q) (he : CobN e) :
    CobN fun args => Item.val (q args) (Item.w d (e args)) :=
  cobN_hor (cobN_radix hq) (cobN_const 1) he (cobN_const 0) (cobN_const 0) (cobN_const _)

theorem cobN_valX (d : Bool) {q e : Args → ℕ} (hq : CobN q) (he : CobN e) :
    CobN fun args => Item.val (q args) (Item.x d (e args)) :=
  cobN_hor (cobN_radix hq) (cobN_const 2) (cobN_const 0) he (cobN_const 0) (cobN_const _)

theorem cobN_valY (d : Bool) {q e : Args → ℕ} (hq : CobN q) (he : CobN e) :
    CobN fun args => Item.val (q args) (Item.y d (e args)) :=
  cobN_hor (cobN_radix hq) (cobN_const 4) (cobN_const 0) (cobN_const 0) he (cobN_const _)

theorem cobN_lit {m v j : Args → ℕ} {b : Args → Bool} (hm : CobN m) (hv : CobN v) (hj : CobN j)
    (hb : CobB b) : CobN fun args => lit (m args) (v args) (j args) (b args) :=
  (cobN_add (cobN_mul (cobN_const 2) (cobN_add (cobN_mul hv hm) hj))
    (cobN_ite hb (cobN_const 0) (cobN_const 1))).of_eq fun args => by simp [lit]

/-! ### The explicit numbers, generically -/

/-- The explicit numbers, with the clause triples `cl` and the further clause occurrences `cr`
as parameters. -/
def numsGen (n m : ℕ) (cl : List (ℕ × ℕ × ℕ)) (cr : List ℕ) : List ℕ :=
  ((tsTrip n m ++ cl ++ gcTrip n m).map Item.trip ++ (List.range (2 * n * m)).map (Item.w false) ++
    (List.range (2 * n * m)).map (Item.x false) ++ (List.range (2 * n * m)).map (Item.y false) ++
    (cl.map (fun t => t.1) ++ (gcTrip n m).map (fun t => t.1)).map (Item.w true) ++
    (tFsec n m ++ cr ++ gcRest n m).map (Item.x true) ++
    (tFthird n m ++ cr ++ gcRest n m).map (Item.y true)).map (Item.val (2 * n * m))

theorem numsOf_eq (n : ℕ) (φ : CNF) :
    numsOf n φ = numsGen n φ.length (clTrip n φ) (clRest n φ) := rfl

/-- The clause triples, literal by literal. -/
def clF (n m : ℕ) : ℕ → ℕ × Bool → Bool → List (ℕ × ℕ × ℕ) :=
  fun j l _ => [(lit m l.1 j l.2, n * m + j, n * m + j)]

/-- The further clause occurrences, literal by literal. -/
def crF (n m : ℕ) : ℕ → ℕ × Bool → Bool → List ℕ :=
  fun j _ last => if last then [] else [n * m + j]

/-- The explicit numbers, computed from the token list. -/
def numsTok (n : ℕ) (T : List ℕ) : List ℕ :=
  numsGen n (nZeros T) (tokLoop (clF n (nZeros T)) T 0) (tokLoop (crF n (nZeros T)) T 0)

theorem map_eq_flatMap_range {α β : Type} (l : List α) (d : α) (f : α → β) :
    l.map f = (List.range l.length).flatMap fun r => [f (l.getD r d)] := by
  rw [← map_range_getD l d f, List.map_eq_flatMap]

theorem replicate_eq_flatMap_range_lt {α : Type} (x : α) (K : ℕ) :
    ∀ L, L < K → List.replicate L x = (List.range L).flatMap fun r =>
      if decide (r + 1 = K) = true then [] else [x]
  | 0, _ => rfl
  | L + 1, h => by
    rw [List.range_succ, List.flatMap_append, ← replicate_eq_flatMap_range_lt x K L (by omega),
      List.replicate_succ']
    simp [show L + 1 ≠ K by omega]

theorem replicate_eq_flatMap_range {α : Type} (L : ℕ) (x : α) :
    List.replicate (L - 1) x = (List.range L).flatMap fun r =>
      if decide (r + 1 = L) = true then [] else [x] := by
  rcases L with _ | L
  · rfl
  · rw [List.range_succ, List.flatMap_append, ← replicate_eq_flatMap_range_lt x _ L (by omega)]
    simp

theorem numsTok_toks (n : ℕ) (φ : CNF) : numsTok n (toks φ) = numsOf n φ := by
  rw [numsTok, nZeros_toks, tokLoop_toks, tokLoop_toks, numsOf_eq]
  congr 1
  · unfold litLoop clTrip clF
    refine List.flatMap_congr fun j _ => ?_
    rw [map_eq_flatMap_range _ (0, false)]
    simp
  · unfold litLoop clRest crF
    refine List.flatMap_congr fun j _ => ?_
    rw [replicate_eq_flatMap_range]
    simp

/-! ### The explicit numbers in flat form -/

theorem map_tokLoop {α β : Type} (F : ℕ → ℕ × Bool → Bool → List α) (g : α → β) (T : List ℕ)
    (z : ℕ) : (tokLoop F T z).map g = tokLoop (fun j l b => (F j l b).map g) T z := by
  unfold tokLoop
  rw [List.map_flatMap]
  refine List.flatMap_congr fun i _ => ?_
  split <;> simp

/-- The explicit numbers, as a concatenation of loops emitting numbers. -/
def numsFlat (n m : ℕ) (T : List ℕ) : List ℕ :=
  ((List.range n).flatMap fun i => (List.range m).flatMap fun j =>
      [Item.val (2 * n * m) (.trip (tT m i j)), Item.val (2 * n * m) (.trip (tF m i j))]) ++
  tokLoop (fun j l _ => [Item.val (2 * n * m) (.trip (lit m l.1 j l.2, n * m + j, n * m + j))])
    T 0 ++
  ((List.range (m * (n - 1))).flatMap fun k => (List.range n).flatMap fun i =>
    (List.range m).flatMap fun j =>
      [Item.val (2 * n * m) (.trip (lit m i j true, n * m + m + k, n * m + m + k)),
       Item.val (2 * n * m) (.trip (lit m i j false, n * m + m + k, n * m + m + k))]) ++
  ((List.range (2 * n * m)).flatMap fun e => [Item.val (2 * n * m) (.w false e)]) ++
  ((List.range (2 * n * m)).flatMap fun e => [Item.val (2 * n * m) (.x false e)]) ++
  ((List.range (2 * n * m)).flatMap fun e => [Item.val (2 * n * m) (.y false e)]) ++
  tokLoop (fun j l _ => [Item.val (2 * n * m) (.w true (lit m l.1 j l.2))]) T 0 ++
  ((List.range (m * (n - 1))).flatMap fun _ => (List.range n).flatMap fun i =>
    (List.range m).flatMap fun j =>
      [Item.val (2 * n * m) (.w true (lit m i j true)),
       Item.val (2 * n * m) (.w true (lit m i j false))]) ++
  ((List.range n).flatMap fun i => (List.range m).flatMap fun j =>
      [Item.val (2 * n * m) (.x true (i * m + (j + 1) % m))]) ++
  tokLoop (fun j _ last => if last then [] else [Item.val (2 * n * m) (.x true (n * m + j))]) T 0 ++
  ((List.range (m * (n - 1))).flatMap fun k => (List.range (2 * n * m - 1)).flatMap fun _ =>
      [Item.val (2 * n * m) (.x true (n * m + m + k))]) ++
  ((List.range n).flatMap fun i => (List.range m).flatMap fun j =>
      [Item.val (2 * n * m) (.y true (i * m + j))]) ++
  tokLoop (fun j _ last => if last then [] else [Item.val (2 * n * m) (.y true (n * m + j))]) T 0 ++
  ((List.range (m * (n - 1))).flatMap fun k => (List.range (2 * n * m - 1)).flatMap fun _ =>
      [Item.val (2 * n * m) (.y true (n * m + m + k))])

theorem replicate_eq_flatMap_const {α : Type} (N : ℕ) (x : α) :
    List.replicate N x = (List.range N).flatMap fun _ => [x] := by
  induction N with
  | zero => rfl
  | succ N ih => rw [List.replicate_succ', ih, List.range_succ, List.flatMap_append]; simp

theorem numsTok_eq_flat (n : ℕ) (T : List ℕ) : numsTok n T = numsFlat n (nZeros T) T := by
  unfold numsTok numsGen numsFlat
  simp only [List.map_append, List.append_assoc, map_tokLoop, List.map_cons, List.map_nil, tsTrip,
    gcTrip, tFsec, tFthird, gcRest, List.map_flatMap, Function.comp_def]
  refine congrArg₂ _ rfl (congrArg₂ _ rfl (congrArg₂ _ rfl ?_))
  simp only [List.map_map, Function.comp_def, clF, crF, List.map_cons, List.map_nil,
    apply_ite (List.map _), replicate_eq_flatMap_const, List.map_flatMap]
  simp only [List.map_eq_flatMap]

/-! ### The stage on codes -/

theorem length_flatMap_range_const {α : Type} (N : ℕ) (F : ℕ → List α) (c : ℕ)
    (h : ∀ i < N, (F i).length = c) : ((List.range N).flatMap F).length = N * c := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih fun i hi => h i (by omega)]
    simp [h N (by omega), Nat.succ_mul]

theorem length_tsTrip (n m : ℕ) : (tsTrip n m).length = 2 * n * m := by
  unfold tsTrip
  rw [length_flatMap_range_const _ _ (m * 2) fun i _ =>
    length_flatMap_range_const _ _ 2 fun j _ => rfl]
  ring

theorem length_gcTrip (n m : ℕ) : (gcTrip n m).length = m * (n - 1) * (2 * n * m) := by
  unfold gcTrip
  rw [length_flatMap_range_const _ _ (n * (m * 2)) fun k _ =>
    length_flatMap_range_const _ _ (m * 2) fun i _ =>
    length_flatMap_range_const _ _ 2 fun j _ => rfl]
  ring

theorem length_clTrip_add (n : ℕ) (φ : CNF) :
    (clTrip n φ).length + φ.length = (toks φ).length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    rw [toks_cons, List.length_append, ← ih]
    unfold clTrip
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.length_append, List.length_map, List.getD_cons_zero, List.getD_cons_succ,
      List.length_cons, List.length_flatMap, Function.comp_def]
    omega

theorem length_gj (n : ℕ) (φ : CNF) : (gj n φ).length =
    2 * n * φ.length + ((toks φ).length - φ.length) + φ.length * (n - 1) * (2 * n * φ.length) := by
  rw [gj, List.length_append, List.length_append, length_tsTrip, length_gcTrip,
    ← length_clTrip_add n φ]
  omega

/-- The list computed by the numerical stage from a list of numbers. -/
def s2List (L : List ℕ) : List ℕ :=
  bigB (2 * L.getD 0 0 * nZeros L.tail) ::
    (2 * L.getD 0 0 * nZeros L.tail + (L.tail.length - nZeros L.tail) +
      nZeros L.tail * (L.getD 0 0 - 1) * (2 * L.getD 0 0 * nZeros L.tail)) ::
    numsFlat (L.getD 0 0) (nZeros L.tail) L.tail

/-- **The numerical stage.** -/
def stage2 (x : List Bool) : List Bool := unl (s2List (parseUnl x))

theorem stage2_code (n : ℕ) (φ : CNF) :
    stage2 (unl (n :: toks φ)) = unl (bigB (gjq n φ) :: (gj n φ).length :: numsOf n φ) := by
  rw [stage2, parseUnl_unl, s2List, List.tail_cons, List.getD_cons_zero,
    ← numsTok_eq_flat, numsTok_toks, nZeros_toks, length_gj, gjq]

end HTN.NPHard
