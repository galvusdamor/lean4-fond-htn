# Alternating sources for the remaining lower bounds

These sources are intended for:
- CB22 Thm 2: ACYC MP strong is EXPSPACE-hard;
- CB22 Thm 5: TR MP strong is 2-EXPTIME-hard;
- ideas "counters": ACYC strong OD is EXPSPACE-hard, TR strong cyclic is 2-EXPTIME-hard.

They are stated as **characterisations of the classes by games**, the form in which
`thm_4_3_6` (Article/TOHard.lean) uses the definition of EXPTIME. An HTN hardness proof
`Cx.Hard 𝒞 X` takes `L ∈ 𝒞`, obtains the fixed machine and polynomials from the
characterisation, and maps `w` in polynomial time to an HTN problem whose solvability is the
existential player's win.

## Formalised (`FondHtn/ATM/`)

### `Savitch.lean`: EXPSPACE = AEXPTIME, the Savitch game

```lean
def SavWin (N : NTM Q Γ) (S : ℕ) : ℕ → Config Q Γ → Config Q Γ → Prop
  | 0, c, c' => (c = c' ∧ c.head < S) ∨ (c.head < S ∧ N.Step c c' ∧ c'.head < S)
  | k + 1, c, c' => ∃ d, SavWin k c d ∧ SavWin k d c'
theorem savWin_iff : SavWin N S k c c' ↔ ∃ n ≤ 2 ^ k, N.ReachesSpace S n c c'
theorem reachesSpace_short : N.ReachesSpace S n c₀ c → ∃ n' ≤ |Q|·S·|Γ|^S, N.ReachesSpace S n' c₀ c
theorem expspace_savWin (hL : Cx.EXPSPACE L) :
    ∃ k (N : NTM (Fin k) TapeSym) p, ∀ w, L w ↔ ∃ c, c.state ∈ N.accept ∧
      SavWin N (2 ^ p(|w|)) (k + p(|w|) + 2·2^p(|w|)) (N.initConfig (w.map some)) c
```

Reading as a game:
- A position is `(j, c, c')`: two configurations with `2^p(|w|)` tape cells, so of exponential
  size, plus a round counter `j`.
- In a round, ∃ names a midpoint `d` (an exponential-size object) and ∀ picks a half.
- After `K = k + p + 2·2^p` rounds, so exponentially many, a local check remains: equality or
  one step.
- The local check can itself be made universal: ∀ picks a cell index of `p(|w|)` bits and the
  triple around it is compared, exactly as in the tableau check.

### `Tableau.lean`: 2-EXPTIME = AEXPSPACE, the CKS tableau game

```lean
def TabWin (F : Option S → S → S → S) (row0 : ℕ → S) : ℕ → ℕ → S → Prop
  | 0, i, σ => σ = row0 i
  | t + 1, i, σ => ∃ l c r, F (if i = 0 then none else some l) c r = σ ∧
      (i ≠ 0 → TabWin t (i - 1) l) ∧ TabWin t i c ∧ TabWin t (i + 1) r
theorem tabWin_iff : TabWin F row0 t i σ ↔ σ = tabF F row0 t i
theorem exptime2_tabWin (hL : Cx.EXPTIME2 L) :
    ∃ k (M : NTM (Fin k) (Option Bool)) q r, M.blank = none ∧ (M deterministic) ∧ ∀ x,
      L x ↔ ∃ i ≤ T x, ∃ qa ∈ M.accept, ∃ γ, TabWin M.F (row0 M q x) (T x) i (some qa, γ)
-- T x = r(|padExp2 q x|), row0 M q x i = (if i = 0 then some q₀ else none, (padExp2 q x).getD i)
```

Reading as a game:
- A position is a claim `(t, i, σ)`. Here `t, i ≤ T x < 2^(c·2^q(|x|))`, so they are numbers
  with **exponentially many bits**.
- In a round, ∃ names the three entries below, and ∀ picks one and the corresponding move of
  `i` (`i-1`, `i` or `i+1`). `t` decreases by one.
- The game lasts `T x` rounds (doubly exponentially many), on exponential-size positions.
- The first row is local: cell `i` of `padExp2 q x = x.flatMap (b ↦ [b,b]) ++ [false,true] ++
  1^(2^2^q)` is computed from `x` and a comparison of `i` with `2|x| + 2 + 2^2^q`.
- Without a padding argument, the same game with `t, i` of `q(|x|)` bits gives the EXPTIME
  source used by `thm_4_3_6`.

## Why exponential-size positions are unavoidable

A game whose positions have polynomial size is decided in alternating polynomial space, i.e. in
EXPTIME, whatever its length. That is the reason the path games of `FondHtn/HardMP/` stop at
EXPTIME (`doc/notes_cb22_thm2.md` §1).
- For EXPSPACE, the positions must carry `2^p` bits: in `SavWin`, a configuration.
- For 2-EXPTIME, the positions must carry numbers of `2^q` bits: in `TabWin`, a counter.
- An HTN encoding must therefore hold such a position in the **task network**, as a sequence of
  `2^n` pending bit tasks, or in a chain of `2^n` primitive tasks executed bit by bit. The FOND
  state can hold only polynomially many facts.

## What an HTN encoding needs from the source (not done)

### Target: CB22 Thm 2 (ACYC, MP strong, EXPSPACE-hard) with `SavWin`
* Represent `c'` (the target configuration) as `2^p` pending tasks, produced by a doubling clock.
* ∃ chooses `d` by decomposing `2^p` cell tasks.
* ∀ chooses the half by a nondeterministic action, recorded honestly (`notes_cb22_thm2.md` §2).
* Depth: `K` rounds of halving. ACYC requires a stratified, bounded nesting, and `K` is
  exponential, so the hierarchy must count rounds with an exponential **counter in the network**
  rather than by nesting depth.
* The commitment obstacle of `notes_cb22_thm2.md` §4 remains: `d` must be fixed *before* ∀ picks
  the half. MP policies can delay decompositions, so the cells of `d` must be forced to execute
  (Route A: lockstep chains) before the half is chosen.

### Target: CB22 Thm 5 (TR, MP strong, 2-EXPTIME-hard) with `TabWin`
* Positions `(t, i, σ)` are two exponential-bit counters and a symbol.
* Tail recursion allows unbounded rounds. Each round decrements `t` and moves `i` by −1, 0 or +1;
  this is exponential-bit counter arithmetic, which the library's EXPSPACE encoding of TR
  (`HtnComplexity/SpaceEnc/`) already performs on tapes of `2^n` cells.
* The ∃ move (three symbols) is a method choice. The ∀ move (which of three) is a
  nondeterministic action with honest recording.
* No commitment problem arises: the claimed symbols are polynomial (constant) size and can be put
  into the **state** before nature's choice. Only `t` and `i` live in the network as counters.
  This makes `TabWin` the more promising first HTN target.
