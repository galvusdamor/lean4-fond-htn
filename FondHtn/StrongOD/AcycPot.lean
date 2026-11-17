import FondHtn.StrongOD.Dec
import FondHtn.Upper.StrongDesc
import HtnComplexity.Article.AcycNExp
import HtnComplexity.Article.MostlyAcycPT
import HtnComplexity.Article.ProgDescSize
/-!
# A potential for decompositions of acyclic problems

With an acyclicity certificate `(R, rk)` (`HTN.Article.AcycCert`) and a bound `B` on the number
of tasks of a method, the potential of a description (`FOND.SOD.pot`) sums over its labels the
weight `1` for a primitive task and `(B + 1) ^ (rk c + 1)` for a compound task `c`.  A
decomposition step on descriptions strictly decreases it (`FOND.SOD.pot_decDesc`), and it bounds
the number of tasks (`FOND.SOD.ids_le_pot`).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

/-- The skeleton of a description: its methods and initial task network only. -/
def skel (p : FProbDesc) : ProbDesc := (([], p.methods), ([], p.tnI, [], []))

theorem skel_methods (p : FProbDesc) : (skel p).methods = p.methods := rfl

theorem skel_tnI (p : FProbDesc) : (skel p).tnI = p.tnI := rfl

section Pot

variable (B : ℕ) (rk : ℕ → ℕ)

/-- The weight of a label. -/
def wt (q : Bool × ℕ) : ℕ := bif q.1 then (B + 1) ^ (rk q.2 + 1) else 1

/-- **The potential** of a description. -/
def pot (d : TnDesc) : ℕ := (d.lbl.map fun q => wt B rk q.2).sum

/-- The invariant of the potential: every task has exactly one label, and the compound labels
are certified names. -/
def PGood (R : List ℕ) (d : TnDesc) : Prop :=
  (d.lbl.map Prod.fst).Perm d.ids ∧ ∀ q ∈ d.lbl, q.2.1 = true → q.2.2 ∈ R

variable {B rk}

theorem one_le_wt (q : Bool × ℕ) : 1 ≤ wt B rk q := by
  unfold wt
  cases q.1
  · simp
  · exact Nat.one_le_pow _ _ (Nat.succ_pos B)

theorem length_le_sum_wt (l : List (ℕ × Bool × ℕ)) :
    l.length ≤ (l.map fun q => wt B rk q.2).sum := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := one_le_wt (B := B) (rk := rk) q.2
    omega

theorem ids_le_pot {R : List ℕ} {d : TnDesc} (hg : PGood R d) : d.ids.length ≤ pot B rk d := by
  rw [← hg.1.length_eq, List.length_map]
  exact length_le_sum_wt _

theorem sum_wt_split {l : List (ℕ × Bool × ℕ)} (hn : (l.map Prod.fst).Nodup) {x : ℕ}
    {v : Bool × ℕ} (hm : (x, v) ∈ l) :
    (l.map fun q => wt B rk q.2).sum =
      ((l.filter fun q => decide (q.1 ≠ x)).map fun q => wt B rk q.2).sum + wt B rk v := by
  induction l with
  | nil => simp at hm
  | cons q l ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hm with rfl | hm
    · have hx : x ∉ l.map Prod.fst := hn.1
      have hf : (l.filter fun q => decide (q.1 ≠ x)) = l := by
        rw [List.filter_eq_self]
        intro r hr
        have : r.1 ≠ x := fun e => hx (e ▸ List.mem_map_of_mem hr)
        simpa using this
      rw [List.filter_cons_of_neg (by simp), hf, List.map_cons, List.sum_cons]
      have : wt B rk (x, v).2 = wt B rk v := rfl
      omega
    · have hqx : q.1 ≠ x := fun e => hn.1 (e ▸ List.mem_map_of_mem hm)
      rw [List.filter_cons_of_pos (by simpa using hqx), List.map_cons, List.map_cons,
        List.sum_cons, List.sum_cons, ih hn.2 hm]
      omega

theorem lookup_of_mem_nodup {β : Type} {l : List (ℕ × β)} (hn : (l.map Prod.fst).Nodup)
    {q : ℕ × β} (hq : q ∈ l) : l.lookup q.1 = some q.2 := by
  induction l with
  | nil => simp at hq
  | cons r l ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hq with rfl | hq
    · simp [List.lookup]
    · have : q.1 ≠ r.1 := fun e => hn.1 (e ▸ List.mem_map_of_mem hq)
      have h' : (q.1 == r.1) = false := by simpa using this
      rw [show r = (r.1, r.2) from rfl, List.lookup_cons, h']
      exact ih hn.2 hq

theorem lookup_of_lblOf {d : TnDesc} {x c : ℕ} (h : lblOf d x = (true, c)) :
    d.lbl.lookup x = some (true, c) := by
  unfold lblOf at h
  cases hl : d.lbl.lookup x with
  | none => rw [hl] at h; simp at h
  | some v => rw [hl] at h; simp at h; rw [h]

theorem lblOf_of_mem {d : TnDesc} (hn : (d.lbl.map Prod.fst).Nodup) {q : ℕ × Bool × ℕ}
    (hq : q ∈ d.lbl) : lblOf d q.1 = q.2 := by
  unfold lblOf
  rw [lookup_of_mem_nodup hn hq]
  rfl

theorem map_fst_filter (l : List (ℕ × Bool × ℕ)) (x : ℕ) :
    (l.filter fun q => decide (q.1 ≠ x)).map Prod.fst = (l.map Prod.fst).filter
      fun y => decide (y ≠ x) := by
  rw [List.filter_map]; rfl

/-- **A decomposition step decreases the potential.** -/
theorem pot_decDesc {p : FProbDesc} {R : List ℕ} (hcert : AcycCert (skel p) R rk)
    (hB : ∀ e ∈ p.methods, e.2.ids.length ≤ B) {prim : ℕ → Prop} {s : List ℕ} {d : TnDesc}
    {x : ℕ} {e : MethodDesc} (hc : CfgInv (s, d)) (hg : PGood R d) (hev : TnValid prim e.2)
    (_hx : x ∈ d.ids) (hl : lblOf d x = (true, e.1)) (he : e ∈ p.methods) :
    PGood R (decDesc d x e) ∧ pot B rk (decDesc d x e) < pot B rk d := by
  set fr := freshIds d.ids e.2.ids.length with hfr
  have hfrn : fr.Nodup := freshIds_nodup _ _
  have hfrl : fr.length = e.2.ids.length := length_freshIds _ _
  have hxm : (x, (true, e.1)) ∈ d.lbl := mem_of_lookup_eq_some (lookup_of_lblOf hl)
  have he1R : e.1 ∈ R := hg.2 _ hxm rfl
  have hcopy : (copyDesc e.2 fr).lbl = e.2.ids.map fun y => (renOf e.2.ids fr y, lblOf e.2 y) := rfl
  refine ⟨⟨?_, fun q hq hq1 => ?_⟩, ?_⟩
  · show (((d.lbl.filter fun q => decide (q.1 ≠ x)) ++ (copyDesc e.2 fr).lbl).map Prod.fst).Perm
      ((d.ids.filter fun y => decide (y ≠ x)) ++ fr)
    rw [List.map_append, map_fst_filter, hcopy, List.map_map]
    refine (hg.1.filter _).append ?_
    refine (List.perm_ext_iff_of_nodup ?_ hfrn).2 fun z => ?_
    · exact hev.nodup.map_on fun a ha b hb h => renOf_inj hev.nodup hfrn hfrl ha hb h
    · simp only [List.mem_map, Function.comp_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact renOf_mem hev.nodup hfrn hfrl hy
      · intro hz
        exact renOf_surj hev.nodup hfrn hfrl hz
  · rcases List.mem_append.1 hq with hq | hq
    · exact hg.2 q (List.mem_filter.1 hq).1 hq1
    · rw [hcopy] at hq
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hq
      exact (hcert.step e he he1R y hy _ (by rw [lblOf_eq_of_fst hq1])).1
  · have hsplit := sum_wt_split (B := B) (rk := rk) (l := d.lbl) hc.lbl_nodup hxm
    have hnew : pot B rk (decDesc d x e) =
        ((d.lbl.filter fun q => decide (q.1 ≠ x)).map fun q => wt B rk q.2).sum +
          (e.2.ids.map fun y => wt B rk (lblOf e.2 y)).sum := by
      show (((d.lbl.filter fun q => decide (q.1 ≠ x)) ++ (copyDesc e.2 fr).lbl).map
        fun q => wt B rk q.2).sum = _
      rw [List.map_append, List.sum_append, hcopy, List.map_map]
      rfl
    have hbound : (e.2.ids.map fun y => wt B rk (lblOf e.2 y)).sum ≤
        e.2.ids.length * (B + 1) ^ rk e.1 := by
      have := List.sum_le_card_nsmul (e.2.ids.map fun y => wt B rk (lblOf e.2 y))
        ((B + 1) ^ rk e.1) (fun n hn => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
          unfold wt
          cases hb : (lblOf e.2 y).1
          · exact Nat.one_le_pow _ _ (Nat.succ_pos B)
          · have hlt := (hcert.step e he he1R y hy _ (lblOf_eq_of_fst hb)).2
            exact Nat.pow_le_pow_right (Nat.succ_pos B) hlt)
      simpa using this
    have h1 : e.2.ids.length * (B + 1) ^ rk e.1 ≤ B * (B + 1) ^ rk e.1 :=
      Nat.mul_le_mul_right _ (hB e he)
    have h2 : wt B rk (true, e.1) = (B + 1) ^ (rk e.1 + 1) := rfl
    have h3 : B * (B + 1) ^ rk e.1 < (B + 1) ^ (rk e.1 + 1) := by
      rw [pow_succ]
      have := Nat.one_le_pow (rk e.1) (B + 1) (Nat.succ_pos B)
      nlinarith
    rw [hnew]
    show _ < (d.lbl.map fun q => wt B rk q.2).sum
    omega

theorem sum_filter_le (l : List (ℕ × Bool × ℕ)) (f : ℕ × Bool × ℕ → Bool) :
    ((l.filter f).map fun q => wt B rk q.2).sum ≤ (l.map fun q => wt B rk q.2).sum :=
  ((List.filter_sublist).map _).sum_le_sum fun _ _ => Nat.zero_le _

/-- Progression keeps the invariant and does not increase the potential. -/
theorem pot_progDesc {R : List ℕ} {d : TnDesc} (hg : PGood R d) (x : ℕ) :
    PGood R (progDesc d x) ∧ pot B rk (progDesc d x) ≤ pot B rk d := by
  refine ⟨⟨?_, fun q hq => hg.2 q (List.mem_filter.1 hq).1⟩, sum_filter_le _ _⟩
  show ((d.lbl.filter fun q => decide (q.1 ≠ x)).map Prod.fst).Perm
    (d.ids.filter fun y => decide (y ≠ x))
  rw [map_fst_filter]
  exact hg.1.filter _

/-- The initial network. -/
theorem pot_d₀ {p : FProbDesc} (hp : p.Valid) {R : List ℕ} (hcert : AcycCert (skel p) R rk)
    {H : ℕ} (hH : ∀ c, rk c ≤ H) :
    PGood R (d₀ p) ∧ pot B rk (d₀ p) ≤ p.tnI.lbl.length * (B + 1) ^ (H + 1) := by
  have hperm := hp.tnI.lbl_perm
  have hn : (p.tnI.lbl.map Prod.fst).Nodup := hperm.nodup_iff.2 hp.tnI.nodup
  refine ⟨⟨hperm, fun q hq hq1 => ?_⟩, ?_⟩
  · have hq' : q ∈ p.tnI.lbl := hq
    refine hcert.init q.1 (hperm.subset (List.mem_map_of_mem hq')) q.2.2 ?_
    show lblOf p.tnI q.1 = _
    rw [lblOf_of_mem hn hq', ← hq1]
  · have := List.sum_le_card_nsmul (p.tnI.lbl.map fun q => wt B rk q.2) ((B + 1) ^ (H + 1))
      (fun n hn => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hn
        unfold wt
        cases q.2.1
        · exact Nat.one_le_pow _ _ (Nat.succ_pos B)
        · exact Nat.pow_le_pow_right (Nat.succ_pos B) (by have := hH q.2.2; omega))
    simpa [pot, d₀] using this

end Pot

end SOD

end FOND
