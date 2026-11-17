# CB22 Thm 5 (TR, MP strong, 2-EXPTIME-hard): progress 2

Continues `doc/notes_cb22_thm5_progress.md` (design "transducer SpaceEnc") and
`doc/notes_cb22_thm5.md`.  P5 (`FondHtn/HardTR/Source.lean`) was already done.

## 1. What is proved (sorry-free, axioms: propext, Classical.choice, Quot.sound)

### `FondHtn/HardTR/WGame.lean` — the soundness layer (generic, 200 lines)

**Design change.**  Soundness is *not* argued on task networks along `MPProg` derivations (the
plan of progress.md §2).  Networks are forgotten:

* `LWin app outs L s` — the **word game** on a language `L : Set (List A)`: win if `[] ∈ L`, or
  play an applicable `a` such that every outcome wins on the residual `{w | a :: w ∈ L}`.  The
  player is stronger than in `MPProg` (no commitment to decompositions); `LWin.mono`.
* **`lwin_of_mpProg_init`** `(hP : P.WF) (h : P.MPProg P.tnI P.init) :
  LWin (fun a s => (P.δ a).Applicable s) (fun a s => (P.δ a).outcomes s)
    {as | (skelAt P P.tnI).domain.NetYield P.tnI as} P.init`
  (general form `lwin_of_mpProg`; proof via soundness of progression search
  `HTN.Problem.isSolutionPlan_of_goalNode` on the skeleton with initial network `tn`).
  Combined with `mpStrongSolvable_iff_mpProg` this gives: strong MP solvable ⇒ word game on
  the refinements of `tn_I` is won.
* `LTS Q A` (step relation, accepting configurations), `LTS.Acc` (the words accepted),
  `LTS.post`, and the **configuration game** `NWin app outs T X s` on *sets* of configurations;
  `NWin.mono`, **`nwin_of_lwin`** (`LWin L s` and `L ⊆ ⋃_{q∈X} Acc q` ⇒ `NWin X s`),
  `NWin.false_of_empty` (if all applicable actions have outcomes).

So soundness of an encoding = (i) the refinements of `tn_I` are accepted by an automaton (an
over-approximation suffices), (ii) analysis of the configuration game of that automaton.

### `FondHtn/HardTR/Round.lean` — the abstract round lemma (920 lines), namespace `FOND.HardTR.TL`

* `Mach G Op En` — parameters: `m` (address bits, `W = 2^m` cells), the transducer
  `opOK : Op → G → Bool → ℕ → Prop` (control, read bit, address), `opEff : Op → G → G`,
  `opW : Op → Bool` (written bit), round-end gadget `endOK : En → G → Prop`,
  `endOut : En → G → Set G` (nature; `endNe` : outcomes nonempty), `finOK : G → Prop`,
  `boot : G → Prop`.
* States `Rec G` = phase `Ph` (`wb k | rv | rb k | op | inc | fin | drain`), counter `c`, writer
  parity `par`, last read bit `sym`, control `g`.  Actions `Act Op En`:
  `wb p k b, rv p γ, rb p k b, op p o, inc p k, wrap p, rend p e, nrd p, dr p, fin`, with
  `Mach.app`/`Mach.outs` (all deterministic except `rend`).  Per position:
  `wb ρ 0..m-1` (address = counter bits) · `rv (!ρ) γ` · `rb (!ρ) (m-1)..0` (address check of the
  tail read) · `op ρ o` · `inc ρ k | wrap ρ`; after `wrap`: phase `fin` with `rend ρ e` or `fin`.
  Boot round: `nrd ρ` instead of `rv`/`rb` (requires `boot g`, sets `sym := false`).
* Threads `Th` (`hd k a, nb a, ic a γ, tv a γ, tb k a, re`) and `Mach.thStep` — the word
  automaton: `hd k a –wb k b→ hd (k+1) (a + b·2^k)`, `hd m a –op o→ ic a (opW o)`,
  `hd m a –nrd→ nb a –op o→ ic a (opW o)`, `ic a γ –inc/wrap→ tv a γ`,
  `tv a γ –rv γ | dr→ tb (m-1) a`, `tb k a –rb k (a.testBit k) | dr→ tb (k-1) a` (done after
  `k = 0`), `re –rend e | dr→ done`.  A loop = multiset of threads (`stepC`: a thread steps, or if
  the multiset is `0` the loop starts a fresh `block` = `W × hd 0 0 + re`).  `Cfg` = one multiset
  per loop + pending finish thread; `Mach.lts`; `Mach.Win X r := NWin M.app M.outs M.lts X r`.
* Canonical configurations: `fm f N` (multiset of `f i`, `i < N`), writer `wF w' c`, reader
  `rF w c`, `cfg ρ S T`, `Mach.start ρ w := cfg ρ 0 (fm (rF w 0) (W+1))`.
* `SRun M rd w' c g g'` — relational transducer run from cell `c` to the end (`rd` read tape,
  `w'` written tape).
* **`Mach.round_sound`** `(hm : 0 < M.m) (hboot : ∀ o g, M.boot (M.opEff o g) ↔ M.boot g)
  (hnb : ¬ M.boot g) (h : M.Win {M.start ρ w} ⟨.wb 0, 0, ρ, y, g⟩) :
  ∃ w' g' y', SRun M w w' 0 g g' ∧ (M.finOK g' ∨ ∃ e, M.endOK e g' ∧
    ∀ g'' ∈ M.endOut e g', M.Win {M.start (!ρ) w'} ⟨.wb 0, 0, !ρ, y', g''⟩)`.
* **`Mach.boot_sound`** — the same from `cfg ρ 0 0` (no tails), with `SRun M (fun _ => false) …`.
* Building blocks: `win_wb`/`win_wbs` (address of the word in progress), `win_rv`,
  `win_rb_succ`, `win_rb_zero` (the read tail is the one of cell `c`: candidate set `Yrb`,
  bits compared top-down, `eq_of_testBit_lt`), `win_read`, `win_nrd`, `win_op`, `win_inc`,
  `win_pos`, `win_pos_boot`, `sweep` (generic induction over positions), `win_end`.

The forcing argument is local: at every step the set of configurations consistent with the
history is a singleton, except during the address check of a read (indexed by the candidate cell).
Counting/summation arguments are not needed.

## 2. What remains

### P3a: the tableau transducer (pure combinatorics, no HTN) — next step

Instantiate `Mach` for the tableau game of `exptime2_tabWin_pow` (`M.F` local rule, entries
`S = Option (Fin k) × Option Bool`), `m = e + 2`, `W = 4B`, `B = 2^e`.  Tape layout: cell `2j`
= bit `j` of `t`, cell `2j+1` = bit `j` of `i` (`2B` bits each, so `i ≤ i₀ + T < 2^(2B)`, no
overflow; `t₀ = 2^B − 1` = ones exactly on cells `< 2B`, i.e. address bit `m-1` clear).

Control `g`: mode (boot/normal), claim `σ`, pending direction `d` (applied to `i` in the next
sweep — nature's choice at the round end cannot be written before), borrow of `t`, carry of `i`,
flags `zt` (`t = 0`), `zi` (new `i = 0`), and the `row0` check (below).  Normal sweep writes
`(t − 1, i_old + d)`; at the end: `fin` needs `zt ∧ R ∧ no carry`, `rend κ` needs `¬zt`, no
carry, `F (zi ? none : l) c r = σ` for the claim `κ = (l,c,r)`; outcomes `d' ∈ {−1,0,1}` (or
`{0,1}` via a separate end action when `zi`), `σ := κ[d']`, `d := d'`, reset flags.  Boot sweep:
writes `t` = (cell `< 2B` ? 1 : 0) via the address bit `m-1`, `i` bits free for `j < B`, 0 above;
boot `rend` claims an accepting `(some qa, γ)`, `d := 0`.

**The `row0` check without disjunctive position tests.**  `opOK` must be a conjunction of
counter-bit tests (one FOND precondition).  `R = (σ = row0 i)` is "`i` lies in one of O(|x|)
intervals with sparse constant endpoints" (`padExp2`: `x` doubled, `01`, `2^2^Q` ones, blanks).
Let the first `op` of the sweep **guess the interval** `k` (existential), and verify
`lo_k ≤ i < hi_k` with LSB-first comparators.  Position dependence by a **schedule**: the 1-bits
of `lo_k`, `hi_k` sit at explicit addresses `a_1 < … < a_r`; *special ops* for `a_{s+1}` require
the exact address (conjunction of `m` bit tests) and schedule counter `s`, *generic ops* test no
address bits and treat the constant bit as 0; at the end require `s = r` — skipping a special
address is then detected.  (Alternative: change the source so that row0 is simpler.)

Soundness theorem to prove: by induction on `t`, using `round_sound`, every won round start with
tape `(t, i_old)` and control `(σ, d)` gives `TabWin t (i_old + d) σ`; `boot_sound` gives the
initial claim.  Use `decB`/`incB` lemmas of `Source.lean` on the interleaved tape (define
`tapeOf t i : ℕ → Bool` and show `SRun` ⇒ written tape = `tapeOf (t-1) (i_old+d)` and the flags).

### P1/P2-instantiation: the HTN encoding

* Methods (all TR; recursion only in `loop p`, last task):
  `main → loop A ∥ loop B ∥ finT`; `finT → [fin]`; `loop p → [block p, loop p] | []`;
  `block p → tree p m ∥ reT p`; `tree p (k+1) → tree p k ∥ tree p k`; `tree p 0 → [bit p 0]`;
  `bit p k → [wb p k b, bit p (k+1), rbT p k b]` (`b : Bool`); `bit p m → [core p]`;
  `core p → [op p o, incT p, rvT p (opW o)] | [nrd p, op p o, incT p, rvT p (opW o)]`;
  `incT p → [inc p k] | [wrap p]`; `rvT p γ → [rv p γ] | [dr p]`;
  `rbT p k b → [rb p k b] | [dr p]`; `reT p → [rend p e] | [dr p]`.
* Language inclusion: `NetYield tn_I ⊆ Acc C₀` with `C₀ = ⟨fun _ => 0, true⟩` — by strong
  induction on the number of decomposition steps with `netYieldN_isPar_iff`,
  `netYieldN_isSeries_iff`, `netYieldN_single_comp` (htn-planning `Interleave/NetYield.lean`);
  needs an "interleaving of accepted words of parallel threads is accepted by the multiset" lemma
  for `stepT` (and the loop/`block` sequencing).
* Facts encoding of `Rec` (one-hot phase, counter bits, parity, sym, the control fields) and the
  commuting lemmas `app ↔ Applicable (enc r)`, `outs ↔ outcomes` (cf. `FondHtn/HardMP/Encoding`:
  `Cfg.enc`, `ASpec`, `toFAct`); then a transfer `NWin` on `Set ℕ` states ⇒ `NWin` on records.
* Descriptions (`FProbDesc`), polynomial-time computability, TR certificate (cf.
  `FondHtn/HardMP/Desc.lean`, `PT.lean`, `Classes.lean`).

### P4: completeness

The word game is only an over-approximation, so completeness needs the real `MPProg` on
networks.  Suggested route: `MPProgH.delay` (`MPStrong/Prog.lean`) gives
`DecompStep tn t m tn' → MPProg tn' s → MPProg tn s` for *any* `t` (graded version), so the
canonical strategy may decompose a whole block eagerly at the round start (method choices are
determined by the tape, the control and the true claims); the remaining play is on a network
"parallel chains (tails) ≺ loop ∥ loop": an explicit description up to isomorphism
(`MPProg.isoVia`; htn-planning `Interleave/GridNet`, `ParallelNet`) and prim steps.  The drain
after `fin` uses the `dr` alternatives and the empty `loop` method.

### P5 assembly, P6 fair

* Assembly with `exptime2_tabWin_pow` and `strongMP_TR_mem` (`MPStrong/TR.lean`).
* Fair (`PlanExMPFair FClass.TR`): the word-game soundness above is for `MPProg` (inductive); for
  fair policies, show that every reachable node of this family has a well-founded measure (`t`,
  then the position in the round, then the drain) so that the fair game implies `MPProg`, as in
  `fair_iff_strong_ACYC`.
