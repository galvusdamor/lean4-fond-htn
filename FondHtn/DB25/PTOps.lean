import FondHtn.DB25.Reduction
import HtnComplexity.PT.DivMod
import HtnComplexity.Article.BinCount
/-!
# Polynomial time: the gadgets

The action descriptions and phases of the register operations are computed in polynomial time.
-/

namespace FOND

namespace DB

open HTN HTN.Syn HTN.Syn.PolyDom PTime

section

variable {α : Type} [BEnc α]

theorem pt_toNat {b : α → Bool} (hb : PT b) : PT fun a => (b a).toNat :=
  (PT.cond hb (PT.const 1) (PT.const 0)).of_eq fun a => by cases b a <;> rfl

theorem pt_lit {v : α → ℕ} {b : α → Bool} (hv : PT v) (hb : PT b) : PT fun a => lit (v a) (b a) :=
  PT.natPair (PT.const 0) (PT.natPair hv (pt_toNat hb))

theorem pt_hlit {v : α → ℕ} {b : α → Bool} (hv : PT v) (hb : PT b) : PT fun a => hlit (v a) (b a) :=
  PT.natPair (PT.const 1) (PT.natPair hv (pt_toNat hb))

theorem pt_qF {q : α → ℕ} (hq : PT q) : PT fun a => qF (q a) := PT.natPair (PT.const 4) hq

theorem pt_setA {r : α → ℕ} {b : α → Bool} (hr : PT r) (hb : PT b) :
    PT fun a => setA (r a) (b a) := by
  unfold setA
  exact PT.pair (PT.const 0) (PT.pair PT.nil (PT.pair PT.nil (PT.single (PT.pair
    (PT.single (pt_lit hr hb)) (PT.single (pt_lit hr (PT.not hb)))))))

theorem pt_natA {r : α → ℕ} (hr : PT r) : PT fun a => natA (r a) := by
  unfold natA
  exact PT.pair (PT.const 0) (PT.pair PT.nil (PT.pair PT.nil (PT.cons (PT.pair
    (PT.single (pt_lit hr (PT.const true))) (PT.single (pt_lit hr (PT.const false))))
    (PT.single (PT.pair (PT.single (pt_lit hr (PT.const false)))
      (PT.single (pt_lit hr (PT.const true))))))))

theorem pt_cpA_lit {s d : α → ℕ} {b : α → Bool} (hs : PT s) (hd : PT d) (hb : PT b) :
    PT fun a => cpA (s a) (lit (d a)) (b a) := by
  unfold cpA
  exact PT.pair (PT.const 0) (PT.pair (PT.single (pt_lit hs hb)) (PT.pair PT.nil (PT.single
    (PT.pair (PT.cons (pt_lit hs (PT.not hb)) (PT.single (pt_lit hd (PT.not hb))))
      (PT.cons (pt_lit hs hb) (PT.single (pt_lit hd hb)))))))

theorem pt_cpA_hlit {s : α → ℕ} {b : α → Bool} (hs : PT s) (hb : PT b) :
    PT fun a => cpA (s a) (hlit (s a)) (b a) := by
  unfold cpA
  exact PT.pair (PT.const 0) (PT.pair (PT.single (pt_lit hs hb)) (PT.pair PT.nil (PT.single
    (PT.pair (PT.cons (pt_lit hs (PT.not hb)) (PT.single (pt_hlit hs (PT.not hb))))
      (PT.cons (pt_lit hs hb) (PT.single (pt_hlit hs hb)))))))

theorem pt_chkA {l : α → ℕ × Bool} (hl : PT l) : PT fun a => chkA (l a) := by
  unfold chkA
  exact PT.pair (PT.const 0) (PT.pair (PT.single (pt_hlit (PT.fst.comp hl) (PT.snd.comp hl)))
    (PT.pair PT.nil (PT.const _)))

theorem pt_hlits {W : α → List ℕ} (hW : PT W) :
    PT fun a => (W a).flatMap fun v => [hlit v true, hlit v false] :=
  PT.flatMap hW (PT.cons (pt_hlit PT.snd (PT.const true)) (PT.single (pt_hlit PT.snd (PT.const false))))

theorem pt_clrA {W : α → List ℕ} (hW : PT W) : PT fun a => clrA (W a) := by
  unfold clrA
  exact PT.pair (PT.const 0) (PT.pair (PT.const _) (PT.pair PT.nil (PT.single (PT.pair
    (pt_hlits hW) PT.nil))))

theorem pt_rstA {W : α → List ℕ} (hW : PT W) : PT fun a => rstA (W a) := by
  unfold rstA
  exact PT.pair (PT.const 0) (PT.pair PT.nil (PT.pair PT.nil (PT.single (PT.pair PT.nil
    (PT.append (PT.const _) (pt_hlits hW))))))

theorem pt_updA {q q' : α → ℕ} {pre sets : α → List (ℕ × Bool)} (hq : PT q) (hq' : PT q')
    (hpre : PT pre) (hsets : PT sets) : PT fun a => updA (q a) (pre a) (q' a) (sets a) := by
  unfold updA
  have hl : PT fun p : α × (ℕ × Bool) => lit p.2.1 p.2.2 := pt_lit (PT.fst.comp PT.snd)
    (PT.snd.comp PT.snd)
  have hl' : PT fun p : α × (ℕ × Bool) => lit p.2.1 (!p.2.2) := pt_lit (PT.fst.comp PT.snd)
    (PT.not (PT.snd.comp PT.snd))
  exact PT.pair (PT.const 0) (PT.pair (PT.cons (pt_qF hq) (PT.map hpre hl)) (PT.pair PT.nil
    (PT.single (PT.pair (PT.cons (pt_qF hq') (PT.map hsets hl))
      (PT.cons (pt_qF hq) (PT.map hsets hl'))))))

theorem pt_cvars {C : α → Clause} (hC : PT C) : PT fun a => cvars (C a) := by
  unfold cvars
  exact PT.dedup (PT.map hC (PT.fst.comp PT.snd))

theorem pt_clausePhases {C : α → Clause} (hC : PT C) : PT fun a => clausePhases (C a) := by
  unfold clausePhases hcopy
  refine PT.append (PT.map (pt_cvars hC) (PT.cons (pt_cpA_hlit PT.snd (PT.const true))
    (PT.single (pt_cpA_hlit PT.snd (PT.const false))))) (PT.cons ?_ (PT.single (PT.single
      (pt_rstA (pt_cvars hC)))))
  exact PT.append (PT.map hC (pt_chkA PT.snd)) (PT.cons (PT.const _) (PT.single (pt_clrA (pt_cvars hC))))

end

end DB

end FOND
