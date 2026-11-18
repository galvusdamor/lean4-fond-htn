import HtnComplexity.Article.ProgDescPT
import HtnComplexity.Article.ShortRun
import HtnPlanning.Article.ProgBoundArticle
import HtnComplexity.Article.TINExp
/-!
# The size of reachable configurations

A configuration reachable from the initial one stands for a network reached by progression
(`HTN.Article.cfgReach_sound`), so a progression bound `n` (Def. 4.3) bounds its number of tasks.
Its ids are numbers of the description or below `n + |p|` (fresh ids are the least unused ones),
its facts lie in `HTN.Article.pfacts`, so (`HTN.Article.sz_cfg_le`)

    |code of c| ≤ 40 (n + |p| + 1)³.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-- **Reachable configurations stand for networks reached by progression.** -/
theorem cfgReach_sound {p : ProbDesc} (hp : p.Valid) {c : PCfg}
    (hrc : Relation.ReflTransGen (fun c c' => c' ∈ succs p c) (initCfg p) c) :
    CfgInv c ∧ ∃ nd, p.toProblem.ProgReach nd ∧ nd.state = {f | f ∈ c.1} ∧
      nd.net.Agree (cfgNet c.2) := by
  induction hrc with
  | refl =>
    refine ⟨inv_initCfg hp, _, .refl, ?_, agree_initCfg hp⟩
    ext f; simp [initCfg, Problem.initPNode, ProbDesc.toProblem]
  | @tail c₁ c₂ _ hs ih =>
    obtain ⟨hc, nd, hnd, hst, hag⟩ := ih
    obtain ⟨hc', π', tn', hstep, hag'⟩ := succs_sound hp hc hs nd.plan
    obtain ⟨B', hstep', hagB⟩ := Problem.ProgStep.agree p.toProblem hstep hag.symm
    refine ⟨hc', ⟨{f | f ∈ c₂.1}, B', π'⟩, hnd.tail ?_, rfl, hagB.symm.trans hag'⟩
    have : nd = ⟨{f | f ∈ c₁.1}, nd.net, nd.plan⟩ := by rw [← hst]
    rw [this]
    exact hstep'

theorem length_ids_le {p : ProbDesc} (hp : p.Valid) {n : ℕ} (hb : p.toProblem.IsHTNProgBound n)
    {c : PCfg} (hrc : Relation.ReflTransGen (fun c c' => c' ∈ succs p c) (initCfg p) c) :
    c.2.ids.length ≤ n := by
  obtain ⟨hc, nd, hnd, -, hag⟩ := cfgReach_sound hp hrc
  have := hb nd hnd
  rw [hag.1] at this
  simpa [cfgNet, List.toFinset_card_of_nodup hc.ids_nodup] using this

/-- The numbers of a configuration. -/
def CfgNums (p : ProbDesc) (N : ℕ) (c : PCfg) : Prop :=
  (∀ x ∈ c.2.ids, x ∈ numsOf p ∨ x < N) ∧ (∀ q ∈ c.2.lbl, q.2.2 ∈ numsOf p) ∧
    ∀ f ∈ c.1, f ∈ pfacts p

theorem cfgReach_nums {p : ProbDesc} (hp : p.Valid) {n : ℕ} (hb : p.toProblem.IsHTNProgBound n)
    {c : PCfg} (hrc : Relation.ReflTransGen (fun c c' => c' ∈ succs p c) (initCfg p) c) :
    CfgNums p (n + sz p) c := by
  induction hrc with
  | refl =>
    refine ⟨fun x hx => Or.inl (mem_numsOf_tnI (List.mem_append_left _ hx)), fun q hq => ?_,
      fun f hf => ?_⟩
    · exact mem_numsOf_tnI (List.mem_append_right _ (List.mem_map.2 ⟨q, hq, rfl⟩))
    · simp only [initCfg, List.mem_dedup] at hf
      simp [pfacts, hf]
  | @tail c₁ c₂ hr hs ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hlen := length_ids_le hp hb hr
    obtain ⟨x, hx, hu, ⟨e, he, hl, rfl⟩ | ⟨a, hl, hr', rfl⟩⟩ := mem_succs.1 hs
    · have hev := hp.methods e he
      refine ⟨fun y hy => ?_, fun q hq => ?_, h3⟩
      · rcases List.mem_append.1 hy with hy | hy
        · exact h1 y (List.mem_filter.1 hy).1
        · right
          have := lt_of_mem_freshIds hy
          have := methods_ids_le e he
          omega
      · rcases List.mem_append.1 hq with hq | hq
        · exact h2 q (List.mem_filter.1 hq).1
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hq
          exact mem_numsOf_method he (List.mem_cons_of_mem _ (List.mem_append_right _
            (lblOf_mem hev hy)))
    · refine ⟨fun y hy => h1 y (List.mem_filter.1 hy).1, fun q hq => h2 q (List.mem_filter.1 hq).1,
        fun f hf => ?_⟩
      have hf' : f ∈ (runStep p (true, c₁.1) a).2 := List.mem_dedup.1 hf
      have : f ∈ {f | f ∈ (runStep p (true, c₁.1) a).2} := hf'
      rw [runStep_state] at this
      exact apply_subset_pfacts p a (fun g hg => h3 g hg) this

theorem length_le_of_nodup_sub {β : Type} [DecidableEq β] {l m : List β} (hl : l.Nodup)
    (h : ∀ x ∈ l, x ∈ m) : l.length ≤ m.length :=
  (hl.subperm h).length_le

theorem sz_le_of_mem_pfacts {p : ProbDesc} {f : ℕ} (h : f ∈ pfacts p) : sz f ≤ sz p := by
  have hp := sz_probDesc p
  simp only [pfacts, List.mem_dedup, List.mem_append, List.mem_flatMap] at h
  rcases h with h | ⟨a, ha, hf⟩
  · have := sz_le_of_mem h
    have : sz p.init = sz p.2.1 := rfl
    omega
  · have h1 := sz_le_of_mem hf
    have h2 : sz a.2.2.2.1 ≤ sz a :=
      (NoHTN.sz_fst_le _).trans ((NoHTN.sz_snd_le _).trans ((NoHTN.sz_snd_le _).trans
        (NoHTN.sz_snd_le _)))
    have h3 := sz_le_of_mem ha
    omega

/-- **The size of a configuration** with at most `n` tasks and ids below `n + |p|`. -/
theorem sz_cfg_le_of {p : ProbDesc} {n : ℕ} {c : PCfg} (hc : CfgInv c) (hN : CfgNums p (n + sz p) c)
    (hL : c.2.ids.length ≤ n) : sz c ≤ 40 * (n + sz p + 1) ^ 3 := by
  obtain ⟨h1, h2, h3⟩ := hN
  set S := sz p with hS
  set Z := n + S + 1 with hZ
  set K := 2 * (n + S) + 1 + S with hKdef
  have hV : (pfacts p).length ≤ S := length_pfacts_le p
  have hid : ∀ x ∈ c.2.ids, sz x ≤ K := fun x hx => by
    rcases h1 x hx with h | h
    · have := sz_le_of_mem_numsOf h; omega
    · have := sz_nat_le_of_lt' h; omega
  have hst : sz c.1 ≤ c.1.length * (2 * S + 2) + 1 := sz_list_le fun f hf => sz_le_of_mem_pfacts (h3 f hf)
  have hstl : c.1.length ≤ S := (length_le_of_nodup_sub hc.st_nodup h3).trans hV
  have hids : sz c.2.ids ≤ c.2.ids.length * (2 * K + 2) + 1 := sz_list_le hid
  have hordmem : ∀ q ∈ c.2.ordList, q ∈ c.2.ids ×ˢ c.2.ids := fun q hq => by
    have hq' : (cfgNet c.2).ord q.1 q.2 := hq
    exact List.mem_product.2 ⟨List.mem_toFinset.1 (hc.wf.mem_left hq'),
      List.mem_toFinset.1 (hc.wf.mem_right hq')⟩
  have hordl : c.2.ordList.length ≤ c.2.ids.length * c.2.ids.length :=
    (length_le_of_nodup_sub hc.ord_nodup hordmem).trans (by rw [List.length_product])
  have hord : sz c.2.ordList ≤ c.2.ordList.length * (2 * (K + K) + 2) + 1 :=
    sz_list_le fun q hq => by
      rw [sz_prod]
      have := hid q.1 (List.mem_product.1 (hordmem q hq)).1
      have := hid q.2 (List.mem_product.1 (hordmem q hq)).2
      omega
  have hlbll : c.2.lbl.length ≤ c.2.ids.length := by
    rw [← List.length_map (f := Prod.fst)]
    exact length_le_of_nodup_sub hc.lbl_nodup fun x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact hc.lbl_mem q hq
  have hlbl : sz c.2.lbl ≤ c.2.lbl.length * (2 * (K + (1 + S)) + 2) + 1 :=
    sz_list_le fun q hq => by
      rw [sz_prod, sz_prod, sz_bool]
      exact Nat.add_le_add (hid q.1 (hc.lbl_mem q hq))
        (Nat.add_le_add_left (sz_le_of_mem_numsOf (h2 q hq)) 1)
  have hsz : sz c = sz c.1 + (sz c.2.ids + (sz c.2.ordList + sz c.2.lbl)) := by
    rw [show sz c = sz c.1 + sz c.2 from sz_prod _ _, sz_tnDesc]
  have hK3 : K ≤ 3 * Z := by omega
  have e1 : c.1.length * (2 * S + 2) ≤ Z * (2 * Z) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : c.2.ids.length * (2 * K + 2) ≤ Z * (8 * Z) := Nat.mul_le_mul (by omega) (by omega)
  have e3 : c.2.ordList.length * (2 * (K + K) + 2) ≤ (Z * Z) * (14 * Z) :=
    Nat.mul_le_mul (hordl.trans (Nat.mul_le_mul (by omega) (by omega))) (by omega)
  have e4 : c.2.lbl.length * (2 * (K + (1 + S)) + 2) ≤ Z * (10 * Z) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hZ1 : 1 ≤ Z := by omega
  rw [hsz]
  nlinarith

/-- **The size of a reachable configuration.** -/
theorem sz_cfg_le {p : ProbDesc} (hp : p.Valid) {n : ℕ} (hb : p.toProblem.IsHTNProgBound n)
    {c : PCfg} (hrc : Relation.ReflTransGen (fun c c' => c' ∈ succs p c) (initCfg p) c) :
    sz c ≤ 40 * (n + sz p + 1) ^ 3 :=
  sz_cfg_le_of (cfgReach_sound hp hrc).1 (cfgReach_nums hp hb hrc) (length_ids_le hp hb hrc)

end Article

end HTN
