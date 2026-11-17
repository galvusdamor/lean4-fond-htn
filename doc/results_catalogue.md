# Catalogue of complexity results for FOND HTN planning

Specification document for the Lean formalisation. Sources:

| Key | Source | Local file |
|---|---|---|
| **CB21** | D. Chen, P. Bercher. *Fully Observable Nondeterministic HTN Planning – Formalisation and Complexity Results.* ICAPS 2021, 74–84. | `doc/00044-ICAPS.ChenD-1.pdf` |
| **CB22** | D. Z. Chen, P. Bercher. *Flexible FOND HTN Planning: A Complexity Analysis.* ICAPS 2022, 26–34. | `doc/00187-ChenD.pdf` |
| **DB25** | P. M. Dekker, G. Behnke. *Hardness of Chosen Length Planning Games and Regular Fixed Methods FOND HTN Planning.* ICAPS 2025. | `doc/Dekker2025Fond.pdf` |
| **IDEAS** | Proof ideas (no full proofs), spring 2025. | `doc/ideas_for_pascal_spring_2025.md` |

Deterministic HTN papers that are cited (not read here; their results are used as black boxes):

| Key | Reference | What is used |
|---|---|---|
| **EHN96** | Erol, Hendler, Nau 1996, *Complexity results for HTN planning*, AMAI 18 | FOD: PO primitive NP-complete; regular PSPACE-complete; general PO undecidable (CFG intersection); progression algorithm for regular problems; encoding of STRIPS planning as a regular HTN |
| **GB11** | Geier, Bercher 2011, IJCAI | undecidability of PO HTN reproduced for the formalism CB21/CB22 use |
| **ABA15** | Alford, Bercher, Aha 2015a, *Tight Bounds for HTN Planning*, ICAPS | FOD: acyclic TO PSPACE-c, acyclic PO NEXPTIME-c, TR TO PSPACE-c, TR PO EXPSPACE-c, arbitrary TO EXPTIME-c; Lemma 3.4 (PO TR progression bound), Lemma 3.6 (TO TR progression bound), Cor 3.2 (acyclic size bound), §4 (exponential "doubling" task construction), Thm 6.1 (counter/TM constructions, NEXPTIME and EXPSPACE hardness) |
| **H+23** | Höller, Lin, Erol, Bercher 2023, *From PCP to HTN Planning Through CFGs*, IPC abstracts | deterministic loop-unrolling HTN is undecidable |
| **DB24** | Dekker, Behnke 2024, *Barely Decidable Fragments of Planning*, ECAI | definition of "loop-unrolling"; "backup and trash" technique |
| others | Bylander 1994; Rintanen 2004; Cimatti et al. 2003; Chandra–Kozen–Stockmeyer 1976/81; Savitch 1970; Cook 1971; Reisch 1980; Hsieh & Tsai 2007 | see §6 |

---

## 0. Conventions and abbreviations

* **TO** = totally ordered problem (tnI and every method network totally ordered), **PO** = partially ordered (no restriction).
* Hierarchy classes: **prim** (tnI primitive), **acyc** (acyclic), **reg** (regular), **TR** (tail-recursive), **arb** (arbitrary). Inclusions: prim ⊂ reg ⊂ TR, prim ⊂ acyc ⊂ TR ⊂ arb.
* **FOD** = deterministic HTN (every action has exactly one effect).
* **FM** = "fixed methods" semantics of CB21 (decompose first, then find a linearisation / a policy for the obtained primitive network). **MP** = "method-based policies" semantics of CB22 (method choice can depend on observed outcomes).
* CB21 solution notions: **weak LD**, **strong LD** (linearisation-dependent, i.e. conformant), **weak OD**, **strong OD** (outcome-dependent, i.e. policy). CB22: **weak**, **strong**, **strong cyclic** (MP).
* Status codes in tables: **C** = complete (membership + hardness), **M** = membership only, **H** = hardness only, **Conj** = conjectured in IDEAS, **semi** = semi-decidable, **undec** = undecidable.
* "Inherited" = the hardness follows because FOD is the special case |eff(a)| = 1 of FOND.
* Alternation identities used everywhere: AP = PSPACE, APSPACE = EXPTIME, AEXPTIME = EXPSPACE, AEXPSPACE = 2-EXPTIME (Chandra, Kozen, Stockmeyer). NPSPACE = PSPACE, NEXPSPACE = EXPSPACE (Savitch).

---

## 1. The three formal settings, and the assumptions they leave implicit

### 1.1 Common core (CB21 Defs 2.1–2.4, CB22 Defs 1–4)

* Task network tn = ⟨T, ≺, α⟩. T is a finite set of task ids, ≺ a strict partial order, α : T → N.
* Domain ⟨F, N_P, N_C, δ, M⟩. δ : N_P → A. An action is a = (pre(a), eff(a)) with pre(a) ⊆ F and eff(a) = {(add_i, del_i) | 1 ≤ i ≤ n}. A **set** of effects, so duplicate outcomes collapse.
* Executability τ(a, s) ⇔ pre(a) ⊆ s. Successors γ(a, s) = {(s \ del_i) ∪ add_i}, undefined if a is not executable. **Add wins over delete.**
* Method m = (c, tn_m) with c ∈ N_C. Decomposition (Def 2.4) replaces task t (α(t) = c) by a fresh isomorphic copy of tn_m; predecessors and successors of t are inherited by every new task.
* Problem ⟨D, s_I, tn_I⟩.

**Implicit assumptions and restrictions, listed so the Lean definitions can fix them explicitly:**

1. **No goal condition.** A solution only has to execute a primitive refinement of tn_I (CB21, CB22, DB25 HTN part). DB25's *planning games* do have a goal, and DB25 encodes it in HTN with the two-task "stop" network (see DB25 Thm 5).
2. **Only positive preconditions** in CB21/CB22. **DB25 and IDEAS use negative preconditions** ("Π−" and "forbid"). DB25 footnote 1 says they can be compiled away in linear time (Gazen & Knoblock 1997). For FOND HTN this needs a small lemma: add a complement fact p̄ for every p. For each outcome (add, del), add p̄ for p ∈ del \ add and delete p̄ for p ∈ add. Make s_I consistent. The compilation keeps task networks, methods and every hierarchy class unchanged, but this has to be proved. **Note:** the strong LD compilation of CB21 Lemma 4.6 is only correct for positive preconditions (see §3.9). Compile negative preconditions away *before* applying it.
3. **Number of effects.** Nothing forbids eff(a) = ∅. Then γ(a, s) = ∅, and every strong notion holds vacuously below that action. DB25's types explicitly allow E = ∅. The game encoding of DB25 Thm 6 handles this consistently: Abélard is stuck and loses. Decide whether to require |eff(a)| ≥ 1. Hardness reductions never need empty effect sets.
4. **No method preconditions** (CB21 discusses them and says the "YoYo style" can be compiled away with an extra first task).
5. **Encoding size** for complexity: CB21 Lemma 4.6 is "polynomial in the number of action effects", so effects are listed explicitly. A succinct representation is never used.
6. **Totally ordered** (CB21 Def 2.14): tn_I and every method network are total. Decomposition keeps total order, so every reachable network is a chain.
7. **Regular** (CB21 Def 3.3, CB22 Def 9, DB25): tn_I and every method network contain at most one compound task, and if there is one, every other task precedes it. CB21/CB22 apply this to tn_I and all methods. DB25 says "every task network of H", which is the same thing.
8. **Stratification / acyclic / tail-recursive** (CB21 Defs 3.4–3.6, CB22 Defs 10–12). These definitions are garbled; see §7, items G1–G3. Use the ABA15 definitions:
   * *acyclic*: the graph c → c′ (c′ occurs in some method of c) has no cycle.
   * *tail-recursive*: there is a total preorder (stratification) ≤ on N_C such that for every method (c, tn) and every compound task t of tn:
     * if t is *last* (every other task of tn precedes t), then α(t) ≤ c;
     * otherwise α(t) < c (strictly lower stratum).
   * The restriction applies to methods only. **tn_I is unrestricted** in TR. This matters for the IDEAS PCP construction, whose initial network has two unordered compound tasks.

### 1.2 CB21 solution notions (fixed methods)

* *Achievable primitive task network*: a primitive network obtained from tn_I by finitely many decompositions. Any compound task may be decomposed, not only "first" ones.
* **Weak LD** (Def 2.7): some linearisation t_1…t_n of an achievable primitive tn and states s_1 = s_I, s_{i+1} ∈ γ(t_i, s_i) with τ(t_i, s_i).
* **Strong LD** (Def 2.7): some linearisation such that, with S_1 = {s_I} and S_i = ⋃_{s∈S_{i−1}} γ(t_{i−1}, s), every s ∈ S_i satisfies pre(t_i). This is a conformant plan.
* **Policy** (Def 2.8): partial function π : 2^T × S → T with π(T′, s) = t only if t ∉ T′ and no t̃ ∈ T \ T′ has t̃ ≺ t. (The intent is "every predecessor of t is in T′". As written it says "t̃ ⊀ t for t̃ not yet executed", which is the same thing.)
* **Execution structure / sequence** (Defs 2.9–2.10) and **weak/strong OD** (Def 2.11): "every [resp. some] execution sequence of K induced by π is complete". *These definitions are broken as written* (see G4). Intended meaning, which is the one to formalise and which coincides with DB25's definition:

  > **FM strong OD** ⇔ ∃ achievable primitive tn such that the pair (tn, s_I) is *solvable*, where (inductively, the least fixed point): (tn, s) is solvable iff tn is empty, or there is a ≺-minimal task t in tn with pre(α(t)) ⊆ s such that (tn \ t, s′) is solvable for **every** s′ ∈ γ(t, s).
  > **FM weak OD**: the same with "for **some** s′ ∈ γ(t, s)" (with γ ≠ ∅).

  This is exactly DB25's "belief state solvable" definition (DB25 §FOND HTN Planning). Positional policies on (executed set, state) suffice because the subgame is determined by (remaining tasks, state).

* Propositions relating them (§3.1–3.4): weak LD ⇔ weak OD (Prop 2.12); strong LD ⇒ strong OD but not conversely (Prop 2.13); for TO problems strong LD ⇔ strong OD (Prop 2.15).

### 1.3 CB22 solution notions (method-based policies, MP)

* **Policy** (Def 5): partial function π : TN × S → T × (M ∪ {ε}) with π(tn, s) = (t, m), t ∈ T(tn), m = ε if t is primitive, m a method for α(t) if t is compound. π may not distinguish isomorphic task networks with the same state.
* **Execution structure** (Def 6) L = ⟨U, V⟩: the least set containing (tn_I, s_I) and closed under:
  * primitive t: (tn \ t, s′) for every s′ ∈ γ(t, s);
  * compound t: (tn′, s) with tn →_{t,m} tn′.

  The structure is taken modulo isomorphism. *Terminal* = no outgoing edge; *goal node* = tn = ∅.
* **Solutions** (Def 7):
  * weak: L finite and some terminal node is a goal node;
  * strong cyclic: every terminal node is a goal node;
  * strong (acyclic): L finite and acyclic and every terminal node is a goal node.
* Execution (Alg. 1); alternating progression search (Alg. 2); bounded graph search (compile to an explicit FOND transition system and run Cimatti et al. 2003).
* Fig. 1 example (tn_I = ⟨a, C⟩, a nondeterministic, C → b | C → c): this has an MP strong solution but no FM strong OD solution. So FM ⊊ MP for strong.
* Recommended formal definition of **MP strong** (equivalent to CB22 Def 7 strong once G6/G7 are fixed): least fixed point. (tn, s) is winning iff:
  * tn = ∅; or
  * some *first* primitive t has pre ⊆ s and every (tn \ t, s′) with s′ ∈ γ(t, s) is winning; or
  * some *first* compound t and method m give a winning (tn′, s).

  Restricting decomposition to first tasks needs a "delaying decompositions is never worse" lemma (G8).

### 1.4 DB25 settings

* **STRIPS problem** P = (P, A, I, G). Actions a = (Π+, Π−, E+, E−), applicable iff Π+ ⊆ S and Π− ∩ S = ∅; γ(S, a) = (S \ E−) ∪ E+.
* **Planning game G(P, r)**: Éloise and Abélard alternate, Éloise first, starting in I. Each move applies an applicable action of A. A player with no applicable action loses. After r actions Éloise wins iff G ⊆ current state. ✓ = (∅, ∅, ∅, ∅) is the "pass" action.
* **Chosen-length problem**: does there exist r ∈ ℕ such that Éloise has a winning strategy in G(P, r)?
* **FOND HTN problem** H = (F, C, O, M, δ, t_0, S_0) with δ(pr) = (Π+, Π−, E), where E is a set of (E+, E−). Solvability is exactly FM strong OD (§1.2), with negative preconditions allowed.
* **loop-unrolling** (DB24): |C| ≤ 1 and |M| ≤ 2. If solvable with non-primitive t_0, one method ("stop") has a primitive network and the other ("cont") may be non-primitive.

---

## 2. Result tables

### 2.1 CB21 Table 1 (fixed methods), reproduced

Columns: FOD (deterministic, for reference) | FM weak (LD = OD, Prop 2.12) | FM strong LD | FM strong OD. In TO rows strong LD = strong OD (Prop 2.15), so one value covers both columns. Superscripts in the FOD column: α = EHN96, β = ABA15, γ = GB11. ∗ = membership only.

| Hierarchy | Order | FOD | Weak (LD=OD) | Strong LD | Strong OD |
|---|---|---|---|---|---|
| primitive | total | P∗ | **NP** [Thm 4.1] C | **P∗** [Cor 4.8] M | (= strong LD) P∗ [Cor 4.8] M |
| primitive | partial | NP^α | **NP** [Cor 4.2] C | **NP** [Thm 4.7] C | **PSPACE** [Thm 5.1] C |
| acyclic | total | PSPACE^β | **PSPACE** [Thm 4.4] C | PSPACE [Cor 4.8] C | (= strong LD) PSPACE [Cor 4.8] C |
| acyclic | partial | NEXPTIME^β | **NEXPTIME** [Thm 4.4] C | **NEXPTIME** [Thm 4.7] C | **EXPSPACE∗** [Thm 5.2] M (hardness known: NEXPTIME, inherited) |
| regular | total | PSPACE^α | **PSPACE** [Cor 4.5] C | PSPACE [Cor 4.8] C | (= strong LD) PSPACE [Cor 4.8] C |
| regular | partial | PSPACE^α | **PSPACE** [Cor 4.5] C | **PSPACE** [Thm 4.7] C | **EXPSPACE∗** [Thm 5.3] M → **C by DB25 Thm 4** |
| tail-rec. | total | PSPACE^β | **PSPACE** [Thm 4.4] C | PSPACE [Cor 4.8] C | (= strong LD) PSPACE [Cor 4.8] C |
| tail-rec. | partial | EXPSPACE^{α,β} | **EXPSPACE** [Thm 4.4] C | **EXPSPACE** [Thm 4.7] C | **semidecidable∗** [Thm 3.1] M (hardness known: EXPSPACE, inherited) |
| arbitrary | total | EXPTIME^β | **EXPTIME** [Thm 4.4] C | EXPTIME [Cor 4.8] C | (= strong LD) EXPTIME [Cor 4.8] C |
| arbitrary | partial | semi- & undecidable^{α,γ} | semi- & undec. [Thm 3.1] C | semi- & undec. [Thm 3.1] C | semi- & undec. [Thm 3.1] C |

Origin of each cell, in one line each:

* Weak column: Thm 4.1 (direct NP proof); Cor 4.2 (guess and check, hardness from 4.1); Thm 4.4 (compile with Lemma 4.3, then use the FOD membership; FOD hardness inherited); Cor 4.5 (progression search, FOD hardness inherited); Thm 3.1 (undecidable).
* Strong LD column: Thm 4.7 (compile with Lemma 4.6 for all classes; FOD hardness inherited).
* Strong OD TO cells: Cor 4.8 = Prop 2.15 + Thm 4.7.
* Strong OD PO cells: Thm 5.1 (direct, PSPACE-c), Thm 5.2 / 5.3 (membership only), Thm 3.1 (semi-decidability).
* Fig. 1 of CB21 lists the explicit polynomial reductions:
  * weak LD = weak OD;
  * strong LD = strong OD (grey, i.e. TO only);
  * FOND weak → FOD (dotted: all classes except primitive and regular);
  * FOND strong LD → FOD (solid: all classes).

### 2.2 CB22 Table 1 (method-based policies), reproduced

| Hierarchy | Order | Weak | Strong | Strong cyclic |
|---|---|---|---|---|
| primitive | total | NP [Prop 2] C | P∗ [Cor 1] M | P∗ [Cor 1] M (same cell) |
| primitive | partial | NP [Prop 2] C | PSPACE [Cor 1] C | PSPACE [Cor 1] C (same cell) |
| acyclic | total | PSPACE [Prop 2] C | **EXPTIME** [Thm 1] C | **EXPTIME** [Thm 1] C |
| acyclic | partial | NEXPTIME [Prop 2] C | **EXPSPACE** [Thm 2] C | **EXPSPACE** [Thm 2] C |
| regular | total | PSPACE [Prop 2] C | **EXPTIME** [Thm 3] C | **EXPTIME** [Thm 3] C |
| regular | partial | PSPACE [Prop 2] C | **EXPTIME** [Thm 3] C | **EXPTIME** [Thm 3] C |
| tail-rec. | total | PSPACE [Prop 2] C | **EXPTIME** [Thm 4] C | **EXPTIME** [Thm 4] C |
| tail-rec. | partial | EXPSPACE [Prop 2] C | **2-EXPTIME** [Thm 5] C | **2-EXPTIME∗** [Thm 5] M (hardness: EXPSPACE) |

Caption: "the general case is undecidable".

* **Arbitrary TO is not in the table.** By Prop 2 + CB21 Thm 4.4, weak MP TO arbitrary is EXPTIME-complete. Strong and strong cyclic MP TO arbitrary are open; IDEAS conjectures 2-EXPTIME-complete.
* Note: **FM and MP complexities are not monotone in each other.** Regular PO is EXPSPACE-complete for FM strong OD (CB21 5.3 + DB25) but EXPTIME-complete for MP strong (CB22 Thm 3). So the more flexible MP notion is *easier* here (assuming EXPTIME ≠ EXPSPACE). This contradicts the spirit of CB22's conclusion ("MP almost always one class harder").

### 2.3 DB25 main results

| # | Statement | Status |
|---|---|---|
| Thm 1 | Chosen-length planning games (∃r: Éloise wins G(P, r)) are EXPSPACE-complete. Remains so for P containing ✓, and for r restricted to even or to odd. | C |
| Thm 2 | Regular FOND HTN (FM strong OD) is in EXPSPACE (= CB21 Thm 5.3). | M (cited) |
| Thm 3 | Loop-unrolling FOND HTN is undecidable (from H+23, deterministic). | undec (inherited) |
| Thm 4 | Regular loop-unrolling FOND HTN (FM strong OD) is EXPSPACE-hard. | H; with Thm 2: **regular PO FM strong OD EXPSPACE-complete** |
| Thm 5 | STRIPS P ↦ regular loop-unrolling H (poly time) with: Éloise wins G(P, r) ⇔ H solvable with exactly r cont applications. | reduction |
| Thm 6 | Regular loop-unrolling H ↦ STRIPS P (poly time) with: Éloise wins G(P, 2(\|T_0\| + r\|T_cont\| + \|T_stop\|)) ⇔ H solvable with r cont applications. | reduction |
| Lemmas 1–3 | Game transformations (add pass action; length r ↦ 2r or 2r+1; restrict to r ≡ 0 mod m). | tools |

### 2.4 IDEAS conjectures

| Idea | Claimed result | Closes |
|---|---|---|
| PCP | FM strong OD, **TR PO** is **undecidable**. | CB21 TR/PO/strong OD cell (currently semi∗) |
| Counters (acyclic) | **acyclic PO** is **EXPSPACE-hard** for FM strong OD, MP strong and MP strong cyclic. | CB21 Thm 5.2 cell (→ EXPSPACE-c); re-proves CB22 Thm 2 hardness |
| Counters (TR) | **TR PO** is **2-EXPTIME-hard** for FM strong OD, MP strong and MP strong cyclic. | CB22 Thm 5 strong cyclic cell (→ 2-EXPTIME-c); a lower bound for FM TR (superseded if PCP works) |
| Total order: membership | MP strong (and, sketched, strong cyclic), **TO arbitrary**, in **2-EXPTIME** (fixpoint over triples (c, s, S′)). | new row of CB22 |
| Total order: hardness | MP strong **TO arbitrary** is **2-EXPTIME-hard** (deterministic TM with 2^{2^n} steps). | new row of CB22 |

### 2.5 Consolidated state of the art (PO = partial order)

FM strong OD (the only FM column with gaps):

| Class | Lower bound | Upper bound | Status |
|---|---|---|---|
| prim PO | PSPACE (CB21 5.1) | PSPACE | C (but see G9: published hardness proof is wrong) |
| acyc PO | NEXPTIME (inherited); Conj EXPSPACE (IDEAS) | EXPSPACE (CB21 5.2) | open |
| reg PO | EXPSPACE (DB25 Thm 4) | EXPSPACE (CB21 5.3) | C |
| TR PO | EXPSPACE (inherited); Conj undecidable (IDEAS PCP) | semi-decidable (CB21 3.1) | open |
| arb PO | undecidable | semi-decidable | C |

MP:

| Class | Notion | Lower | Upper | Status |
|---|---|---|---|---|
| TR PO | strong cyclic | EXPSPACE; Conj 2-EXPTIME | 2-EXPTIME | open |
| arb TO | strong | EXPTIME (from TR TO); Conj 2-EXPTIME | none published; Conj 2-EXPTIME | open |
| arb TO | strong cyclic | EXPTIME | none published; IDEAS sketch incomplete | open |
| arb PO | weak/strong/strong cyclic | undecidable (inherited; strong cyclic needs G6 fixed) | semi-decidable for weak and strong (enumerate finite policies; not stated in CB22) | |

---

## 3. CB21, result by result

### 3.1 Prop 2.12 — weak LD ⇔ weak OD
**Statement.** For any FOND HTN problem and any primitive tn, there is a linearisation that is a weak LD solution iff there is a policy for tn that is a weak OD solution.
**Proof.**
* (⇒) Given a linearisation and witnessing states s_1…s_n, define π(T_i, s_i) = t_{i+1} with T_i = {t_1..t_{i−1}} (index shift is sloppy in the paper). The path ⟨t_1, s_1⟩…⟨t_n, s_n⟩ is a complete execution sequence.
* (⇐) A complete execution sequence gives the linearisation.

**Use.** Collapses the weak columns.

### 3.2 Prop 2.13 — strong LD ⇒ strong OD, not conversely
**Proof.**
* (⇒) Define π on all (T_i, s) with s ∈ S_i.
* (⇍) Counterexample: F = {1, 2}, N_P = {a, b, c}.
  * a = (∅, {({1}, ∅), ({2}, ∅)}), b = ({1}, {2}, ∅), c = ({2}, {1}, ∅).
  * s_I = ∅, T = {t_1, t_2, t_3} with t_1 ≺ t_2, t_1 ≺ t_3, α = (a, b, c).
  * Policy: after a, run b if 1 holds, else c; then the other one.
  * Neither linearisation is conformant.
* CB22 Fig. 2/3 reuses the example with b/c preconditions swapped.

### 3.3 Prop 2.15 — TO: strong LD ⇔ strong OD
**Proof.** In a TO problem every achievable primitive network is a chain, so the only candidate policy follows the chain, which is the linearisation. *Formalisation:* show that decomposition preserves totality, then that solvability of a chain is the same as conformant executability of that chain.

### 3.4 Prop 2.16 — verifying a policy is in P (in |π|)
DFS on the execution structure. Used informally in Thm 5.3.

### 3.5 Thm 3.1 — arbitrary PO: semi-decidable and undecidable for {weak, strong} × {LD, OD}
**Hardness:** inherited from FOD undecidability (EHN96: reduction from emptiness of the intersection of two CFG languages, PO; GB11 for this formalism).
**Membership (semi-decidability):** BFS over decomposition sequences. For each achievable primitive network, decide the solution notion; this is decidable by Cor 4.2 / Thm 4.7 / Thm 5.1.
**Formalisation note:** "semi-decidable" needs a computability framework (e.g. Mathlib's `Computable`/`RePred`). Probably state it as "the set of solvable problems is r.e." and undecidability by computable reduction from a known undecidable problem; the CFG intersection undecidability would itself be an axiom or import.

### 3.6 Thm 4.1 — TO primitive weak: NP-complete
**Membership:** guess one outcome per task of the unique chain; check executability in linear time.
**Hardness:** from SAT. Variables x_1..x_n, clauses C = {c_1..c_m}.
* F = C (one fact per clause); N_P = {e_1, …, e_n, k}.
* e_i = (∅, {({c_j | x_i ∈ c_j}, ∅), ({c_j | ¬x_i ∈ c_j}, ∅)}): two outcomes, add the clauses satisfied by x_i = true resp. false.
* k = (C, ∅, ∅): precondition is all clauses.
* s_I = ∅, tn_I = chain e_1 ≺ … ≺ e_n ≺ k.
* Weak solution ⇔ a choice of outcomes makes all clauses true ⇔ SAT.

Only positive preconditions, ≤ 2 outcomes, no deletes. FOD TO primitive is in P, so this is a genuine jump.

### 3.7 Cor 4.2 — PO primitive weak: NP-complete
**Membership:** guess a linearisation and outcomes, then check. **Hardness:** from Thm 4.1 (TO is a special case; the paper does not state this, but the table cell is "complete"). FOD PO primitive is NP-hard too (EHN96).

### 3.8 Lemma 4.3 — weak compilation FOND → FOD
**Construction.** For each primitive name t_i with δ(t_i) = a_i having outcomes (add_j, del_j), j = 1..n_i:
* new compound name c_i;
* new deterministic primitive names t′_{i,j} with δ(t′_{i,j}) = (pre(a_i), add_j(a_i), del_j(a_i));
* methods m_{i,j} = (c_i, ⟨{u}, ∅, u ↦ t′_{i,j}⟩).

Replace every occurrence of t_i (in tn_I and in method networks) by c_i. The size grows linearly in the number of effects.

**Correctness:** a weak solution picks outcomes, which correspond to method choices for the c_i, and vice versa.

**Preserves:** acyclic (put all c_i on a new bottom stratum) and TO. **Tail-recursive only under the ABA15 reading of "last"** (see G3).

**Destroys:** primitivity (the network now has compound tasks) and regularity (several compound tasks per method).

### 3.9 Thm 4.4 — weak, for arbitrary / acyclic / TR: same complexity as FOD
**Membership:** Lemma 4.3 plus the FOD upper bound of the same class:
* ABA15: acyclic TO PSPACE, acyclic PO NEXPTIME, TR TO PSPACE, TR PO EXPSPACE, arbitrary TO EXPTIME;
* EHN96/GB11: arbitrary PO semi-decidable.

**Hardness:** inherited from the same FOD results.

**Implicit:** the compilation keeps TO, and the FOD results are in a formalism with positive preconditions and no goal.

### 3.10 Cor 4.5 — regular weak: same as FOD (PSPACE-complete, TO and PO)
**Membership (paper):** "the progression search of EHN96 on the compiled problem uses the same space, because the new compound tasks are replaced by a single primitive". This is vague; the compiled problem is not regular.
**Cleaner proof for formalisation:** run nondeterministic progression directly on the FOND regular problem.
* Keep (current network, state).
* Each step either executes a ≺-minimal primitive task, guessing one outcome, or decomposes the unique compound task once it is the only remaining task.
* In a regular problem the current network never exceeds max(|tn_I|, max method size), so this is NPSPACE = PSPACE.

**Hardness:** inherited (EHN96: regular FOD is PSPACE-hard by encoding STRIPS plan existence).

### 3.11 Lemma 4.6 — strong LD compilation FOND → FOD (all classes preserved)
**Construction.**
1. Normalise every outcome: del_j := del_j \ add_j. This is semantically neutral because add wins.
2. Replace each action a by the deterministic action a′ = (pre(a), ⋂_j add_j(a), ⋃_j del_j(a)).

Methods and task networks are untouched, so primitive, TO, acyclic, regular, TR and arbitrary are all preserved.

**Correctness (paper's argument is hand-wavy, see G10). A precise invariant:** for any linearisation t_1…t_n, if s′_i is the state of the deterministic run, then s′_i = ⋂ S_i, where S_i is the set of possible FOND states (with ⋂∅ := F). Proof of the inductive step:
* f ∈ ⋂_{s∈S, j} ((s \ del_j) ∪ add_j) ⇔ ∀j: f ∈ add_j ∨ (f ∈ ⋂S ∧ f ∉ del_j).
* Using add_j ∩ del_j = ∅ this is equivalent to (f ∈ ⋂S ∧ ∀j f ∉ del_j) ∨ (∀j f ∈ add_j), which is (⋂S \ ⋃del_j) ∪ ⋂add_j.
* Preconditions are positive, so "pre ⊆ s for all s ∈ S_i" ⇔ "pre ⊆ ⋂S_i".

Hence: strong LD linearisation in P ⇔ executable linearisation in the compiled FOD problem. **Fails with negative preconditions**; also uses that actions are not applied in states where they are inapplicable.

### 3.12 Thm 4.7 — strong LD: same complexity as FOD for every class
Lemma 4.6 plus the FOD results:
* prim PO NP;
* acyc NEXPTIME / PSPACE;
* reg PSPACE;
* TR EXPSPACE / PSPACE;
* arb undecidable / EXPTIME;
* prim TO P (membership only).

Hardness is inherited.

### 3.13 Cor 4.8 — TO strong OD: same as FOD
Prop 2.15 + Thm 4.7. Gives TO prim P∗, TO acyc PSPACE, TO reg PSPACE, TO TR PSPACE, TO arb EXPTIME.

### 3.14 Thm 5.1 — PO primitive strong OD: PSPACE-complete
**Membership:** an ATM with polynomial running time (AP = PSPACE). For n = |T| rounds:
1. existentially choose a task t_{i_k} that has not been executed and whose predecessors have all been executed;
2. check pre ⊆ current state;
3. universally choose an outcome and update the state.

Accept when all tasks are executed. Equivalently: the recursive solvability game of §1.2 has depth n and polynomial-size positions, so it can be evaluated in PSPACE.

**Hardness (as published):** from the (m, n, k)-game: does player 1 have a winning strategy for k-in-a-row on an m×n board? The paper claims PSPACE-complete for k ≥ 4, citing Hsieh & Tsai 2007 (with p = q = 1) and Reisch 1980.
* Squares i = 1..mn. L is the set of k-lines (each λ ⊆ {1..mn}, one fact per λ).
* F = {x_i, ¬x_i, o_i, ¬o_i} ∪ L ∪ {R, C}. Here "¬x_i" etc. are ordinary facts.
* Actions (only turn_i is nondeterministic):
  * turn_i = ({¬x_i}, {({x_i, o_j}, {¬x_i, ¬o_j}) | 1 ≤ j ≤ mn}): P1 plays i, P2 replies at j;
  * fin_turn_i = ({¬x_i, ¬o_i, R}, {x_i}, {R}): P1's final move, no reply;
  * win_λ = ({x_i | i ∈ λ}, {x_j, ¬x_j | all j}, ∅);
  * not_lose_i = ({¬o_i}, {λ ∈ L | i ∈ λ}, ∅);
  * not_lose_0 = (L, {C}, ∅);
  * illegal_i = ({x_i, o_i}, {C}, ∅);
  * clear = ({C}, F, ∅).
* tn_I: one task per name above except clear, plus N = |L| + 4mn + 1 copies of clear. Order: win_λ ≺ not_lose_i for all λ, i; nothing else.
* s_I = {¬x_i, ¬o_i | all i} ∪ {R}.
* Intended phases: (1) play; (2) a win_λ fires, then all win_λ, then not_lose_i for i with ¬o_i, then not_lose_0 gives C (meaning P2 has no complete line); (3) the clear copies make everything executable.
* P2 placing a stone on an X square: illegal fires, C, escape (allowed). P2 placing on his own square amounts to P2 passing (claimed harmless).

**This construction is incorrect as written** (G9): P1 can trigger `illegal` by playing onto an O square; `fin_turn` gives P1 a free extra move at any time; win_λ re-enables `illegal` and so bypasses the not-lose check. Also |L| ≤ 4mn, not 3mn. A corrected version or a different source problem (TQBF, or bounded-length planning games) is needed for the formalisation.

### 3.15 Thm 5.2 — acyclic PO strong OD: in EXPSPACE
**Algorithm:**
1. Nondeterministically apply decompositions until the network is primitive. With acyclic methods, after h rounds of "decompose all compound tasks" the network is primitive, so its size is ≤ |tn_I| · k^h, with k the largest method size and h ≤ |M| (any bound on the decomposition depth works, e.g. the number of strata or ABA15 Cor 3.2: m^{k+1}).
2. Run the PSPACE procedure of Thm 5.1 on this exponential-size network, in exponential space.

NEXPSPACE = EXPSPACE. **Hardness:** only NEXPTIME (inherited). The table marks membership only. IDEAS conjectures EXPSPACE-hardness.

### 3.16 Thm 5.3 — regular PO strong OD: in EXPSPACE
**Structural fact used:** in a regular problem every achievable primitive network is a sequence of blocks B_1 ≺ B_2 ≺ … ≺ B_ℓ. B_1 is the primitive part of tn_I, B_{i+1} the primitive part of the method applied to the compound task of layer i. Every task of B_i precedes every task of B_{i+1}, because the compound task is last and decomposition inherits ordering. Each block has polynomial size.
**Algorithm:** keep tn (current regular network), S_A (possible start states, initially {s_I}) and S_B. Loop:
1. tn_P := primitive part of tn.
2. For every s ∈ S_A (the paper writes "s ∈ A", a typo): guess a policy π_s for tn_P from s, verify it is strong OD from s (Prop 2.16, relativised to start state s), and add the set of its leaf states to S_B. If verification fails, reject the branch.
3. If tn has no compound task, accept. Otherwise S_A := S_B, S_B := ∅, tn := the compound task alone.
4. Guess a method for it, apply it, and go to 1.

**Space:** S_A, S_B ⊆ 2^F are exponential; a policy for a polynomial-size block is exponential. So NEXPSPACE = EXPSPACE.
**Correctness argument (sketch in paper):** strong OD policies for a block sequence decompose into per-block policies, connected by the sets of reachable leaf states. FM is essential: one method sequence for all branches.
**Hardness:** DB25 Thm 4 makes this EXPSPACE-complete. DB25's Alg. 1 is this algorithm specialised to games.
**Formal note:** Replacing "guess a policy" by the deterministic PSPACE check of Thm 5.1 per start state gives a cleaner proof. Compute S_B as the union, over s ∈ S_A, of the leaf sets of *some* strong policy. Picking per s any strong policy is fine because only membership of leaves in later winning sets matters. **But careful:** the leaf set depends on the chosen policy, and a bad choice can make later layers fail. The nondeterministic guess handles this; a deterministic version must range over all achievable leaf sets, or (better) work backwards. Backward version: W_ℓ = set of states from which the remaining layers are solvable. "Block B solvable from s with all leaves in W" is a PSPACE-style check. Iterating backwards needs the method sequence; in the nondeterministic setting just guess it.

---

## 4. CB22, result by result

### 4.1 Prop 1 — primitive problems: MP definitions = FM definitions
No methods, so an MP policy only executes primitives. For weak, both are "some executable sequence under favourable outcomes"; for strong, both are the recursive solvability of §1.2. Strong = strong cyclic for primitive problems because the network strictly shrinks, so L is finite and acyclic.

### 4.2 Cor 1 — primitive strong / strong cyclic MP: PO PSPACE-complete, TO in P
From Prop 1 + CB21 Thm 5.1 (PO) and CB21 Cor 4.8 (TO, P membership only). **Inherits G9** (the PSPACE-hardness proof of CB21 5.1).

### 4.3 Prop 2 — weak MP = weak FM (existence equivalence)
* From an MP weak trace, take its method applications to get an FM solution.
* From an FM weak solution, first apply all its methods, then follow its linearisation; this gives an MP policy with finite L.

Subtlety: the MP policy must not visit two isomorphic (tn, s); choose a trace without repetitions, e.g. a shortest one.
**Consequence:** the weak column equals CB21's weak column (Thms 4.1/4.2/4.4/4.5): prim NP, acyc PSPACE/NEXPTIME, reg PSPACE, TR PSPACE/EXPSPACE, and also arb TO EXPTIME, arb PO undecidable.

### 4.4 Alg. 2 — alternating strong progression search
StrongPlanExistence(tn, s, M, V):
* accept if tn = ∅;
* reject if (tn, s) ∈ V (up to isomorphism); add (tn, s) to V;
* existentially guess a *first* task t (no predecessors);
* if t is primitive: reject unless pre ⊆ s; then universally over s′ ∈ γ(t, s), recurse on (tn \ t, s′);
* if t is compound: existentially guess a method, decompose, recurse.

V is per branch (cycle detection along a path). Claimed: "remove V for strong cyclic"; that is wrong in general (G7).

### 4.5 Bounded graph search
* Build the explicit FOND transition system ⟨S, A, I, G⟩:
  * S = TN_R × 2^F, where TN_R is the set of task networks reachable by progression (first primitive executed / first compound decomposed), up to isomorphism;
  * I = (tn_I, s_I); G = {(∅, s)};
  * actions: for each first primitive t executable in s_α, the transition (σ_α, {(tn_α \ t, s_i) | s_i ∈ γ(t, s_α)}) (the paper writes τ for γ); for each first compound t and method, the deterministic transition to (tn_β, s_α).
* Solve with Cimatti et al. 2003 weak / strong / strong cyclic algorithms, polynomial in the graph.
* Cost: |TN_R| · 2^{|F|} · (isomorphism test).

### 4.6 Thm 1 — TO acyclic MP strong / strong cyclic: EXPTIME-complete
**Membership:**
* Acyclic means no (tn, s) recurs, so strong = strong cyclic and V can be dropped.
* Under TO progression the network has polynomial size (ABA15 Lemma 3.6 for TO TR, k + r·h).
* So Alg. 2 is an APSPACE procedure, and APSPACE = EXPTIME.

**Hardness (outline only):** a polynomial-space ATM A on input w.
* Facts are Bylander-style: state facts, tape cell contents, head position, polynomially many.
* Every ATM step is a primitive task:
  * in a ∀ state, one **nondeterministic** task whose outcomes are all successor configurations;
  * in an ∃ state, one **deterministic** task per transition (the planner chooses).
* Exponentially many steps with the ABA15 §4 doubling hierarchy:
  * compound 2^k·sim, 0 < k ≤ n, each with one method → ⟨2^{k−1}·sim, 2^{k−1}·sim⟩ (TO);
  * 1·sim has one method → tn(p) for every primitive task p, plus one method → tn_∅;
  * tn_I = tn(2^n·sim) with 2^n ≥ number of configurations C = |Q|·(|Γ|+1)^k·k.
* MP is needed because which ∃-task comes next depends on earlier ∀-outcomes.

**Gaps:** no acceptance check is stated (see G11). Nothing forces the run to end in an accepting state, since 1·sim → tn_∅ lets the planner stop at any time. A final task requiring "accepting state" is needed, and once an accepting state is reached the remaining 1·sim must be emptied. Also unspecified: preconditions that tie the chosen task to the current (state, head, symbol).

### 4.7 Thm 2 — PO acyclic MP strong / strong cyclic: EXPSPACE-complete
**Membership:**
* Strong = strong cyclic (acyclic). The fully decomposed network has size ≤ m^{k+1} (ABA15 Cor 3.2).
* Alg. 2 therefore halts within exponentially many steps, each on an exponential-size network.
* AEXPTIME = EXPSPACE.

**Hardness (outline only):** extend ABA15 Thm 6.1 (acyclic PO NEXPTIME-hardness from an exponential-time NTM) to an exponential-time ATM, giving AEXPTIME-hardness.
* ABA15 represents a computation as three synchronised totally ordered chains of exponentially many tasks: the tape-symbol sequence, a copy-check chain, and a head/transition chain.
* The modification adds nondeterministic step∀ tasks next to the deterministic step∃ tasks.
* It assumes every universal transition moves the head in the same direction; this can be compiled away with extra states.
* MP lets the planner choose the decompositions of the 2nd/3rd chains after seeing outcomes.

**Gaps:** sketch only; ABA15 Thm 6.1 has to be redone in full. The paper calls this a "logarithmic reduction", which is misleading: it is a polynomial reduction that represents exponential tapes implicitly. IDEAS "Counters" proposes an alternative (§5.2).

### 4.8 Thm 3 — regular (TO and PO) MP strong / strong cyclic: EXPTIME-complete
**Membership:**
* Bounded graph search. TN_R for regular problems is exponential: the remaining subset of one method's primitive tasks plus the compound task, so at most (number of methods + 1) · 2^{max method size} networks.
* The graph has |TN_R| · 2^{|F|} nodes; Cimatti's algorithms run in time polynomial in the graph.
* With isomorphism tests the total is still EXPTIME.

**Hardness:** encode FOND STRIPS strong (resp. strong cyclic) plan existence, which is EXPTIME-complete (Rintanen 2004; also Littman 1997), as in EHN96's deterministic encoding:
* compound task `repeat` with one method [a, repeat] per action a (a nondeterministic), and one method [done];
* `done` is a primitive task with precondition = goal;
* tn_I = [repeat].

TO, so it gives both TO and PO hardness.

**Implicit:** the FOND source problem must use positive preconditions and a conjunctive goal (check that the cited EXPTIME-hardness holds for that fragment). The "repeat → [done]" method is not explicitly mentioned. Strong cyclic correspondence needs the fixed strong-cyclic definition (G6).

### 4.9 Thm 4 — TO tail-recursive MP strong / strong cyclic: EXPTIME-complete
**Membership:**
* Under TO progression the network size is ≤ m = k + r·h (ABA15 Lemma 3.6: k initial tasks, r max method size, h stratification height).
* TO networks are words over n = |N_P ∪ N_C| names, so |TN_R| ≤ Σ_{i≤m} n^i ≤ (m+1) n^m. The paper's "i^n" is an index typo.
* Graph size n^m · 2^{|F|}, so EXPTIME.

**Hardness:** from Thm 3 (TO regular ⊂ TO TR).

### 4.10 Thm 5 — PO tail-recursive MP: strong 2-EXPTIME-complete; strong cyclic in 2-EXPTIME and EXPSPACE-hard
**Membership:**
* Progression network size ≤ m = k · r^h, which is exponential (ABA15 Lemma 3.4).
* |TN_R| ≤ Σ_{i≤m} n^i · 2^{i²} ≤ (m+1) · n^m · 2^{m²}: partial orders on i labelled vertices ≤ directed graphs ≤ 2^{i²}. Again the paper has index typos.
* So the graph is doubly exponential and the search is 2-EXPTIME.

**Hardness:**
* Strong cyclic: EXPSPACE, inherited from deterministic TR PO (ABA15). Requires "deterministic strong cyclic = plain plan existence", which fails under the literal Def 7 (G6).
* Strong: extend the ABA15 EXPSPACE-hardness (TR PO, exponential-space TM, unbounded time) to exponential-space ATMs (AEXPSPACE = 2-EXPTIME) "in the same fashion as Thm 2". Outline only.

---

## 5. DB25, result by result

### 5.1 Lemma 1 — adding a pass action ✓
**(1) Even r.** P′ = (P ⊔ {∃, ⋆, g}, A′, I′, {g}). For each a = (Π+, Π−, E+, E−) ∈ A, A′_a contains:
* Éloise variant (1): (Π+ ⊔ {⋆, ∃}, Π−, E+ ⊔ {g}, E− ⊔ {∃});
* Abélard variant: (Π+ ⊔ {⋆}, Π− ⊔ {∃}, E+ ⊔ {∃}, E−);
* if E− ∩ G ≠ ∅, also variant (2): (Π+ ⊔ {⋆}, Π− ⊔ {∃}, E+ ⊔ {∃}, E− ⊔ {g});
* otherwise, for each p ∈ G \ (Π+ ∪ E+), variant (3): (Π+ ⊔ {⋆}, Π− ∪ {p, ∃}, E+ ⊔ {∃}, E− ⊔ {g}).

A′ = {✓, ({⋆, ∃}, ∅, ∅, {⋆, g}), ({⋆}, {∃}, {g}, {⋆})} ⊔ ⋃_a A′_a. The last two are the ⋆-deleting "refutation" actions:
* ({⋆}, {∃}, {g}, {⋆}): if it is Éloise's turn but ∃ is false, she deletes ⋆ and adds g;
* ({⋆, ∃}, ∅, ∅, {⋆, g}): Abélard's counterpart.

I′ = I ⊔ {∃, ⋆} plus g if G ⊆ I.
Idea: playing ✓ lets the opponent win via a refutation action. Éloise's last move sets g; Abélard can delete g iff he can falsify the goal.

**(2) Odd r:** G′ = G ⊔ {g}, and the ⋆-deleting action that adds g also adds G.
**(3) All r, with an action without preconditions:** as (2), but replace ✓ by (∅, ∅, G, ∅).
**Proof status:** informal. Needs a careful game-equivalence proof by induction on r.

### 5.2 Lemma 2 — length scaling r ↦ 2r (and 2r+1)
P′ = (P ⊔ {∃, w}, A′, I ⊔ {∃}, G).
* For each a, A′_a contains (4) (Π+ ⊔ {∃}, Π− ⊔ {w}, E+ ⊔ {w}, E− ⊔ {∃}) and (5) (Π+, Π− ⊔ {∃, w}, E+, E− ⊔ {∃}).
* Plus the dummies ({w}, {∃}, {∃}, ∅) and ({∃, w}, ∅, ∅, {∃, w}).

Four turns of P′ simulate two turns of P. State S after r turns corresponds to S ⊔ {∃} (r even) or S ⊔ {∃, w} (r odd) after 2r turns.
(2) for 2r+1: G′ = G ⊔ {g, g′}, with a_end = ({∃}, {w, g′}, {g, g′}, ∅) and the refutation ({g}, ∅, ∅, {g}).

### 5.3 Lemma 3 — restricting to r ≡ 0 (mod m), m in unary
* P′ = P ⊔ {p_k | k ∈ ℤ/m}.
* For each action and each k, a copy with extra precondition p_k, adding p_{k+1} and deleting p_k.
* I′ = I ⊔ {p_0}, G′ = G ⊔ {p_0}.

Éloise wins G(P′, r) ⇔ Éloise wins G(P, r) ∧ r ≡ 0 mod m. The counter is also used as a "turn counter" so that the hardness proof can restrict which actions are legal at which position of a cycle.

### 5.4 Thm 1 — chosen-length planning games are EXPSPACE-complete

**Membership (Alg. 1).** Let 𝒮_0 = {S ⊆ P | G ⊆ S}. The invariant is 𝒮_r = {S | Éloise wins G(P_S, 2r)}. Update:

𝒮_{r+1} = {S | ∃a applicable in S, ∀b applicable in γ(S, a): γ(γ(S, a), b) ∈ 𝒮_r}.

(If Abélard has no applicable reply, Éloise wins vacuously.)
* Answer yes as soon as I ∈ 𝒮_r.
* The sequence (𝒮_r) is generated by a deterministic map on 2^{2^{|P|}} values, so it is eventually periodic. Stop after 2^{2^{|P|}} iterations, with a binary counter in exponential space.
* Each 𝒮_r needs O(2^{|P|}) bits. Keep only the old and new set.
* For odd lengths, start with 𝒮 = {S | ∃a: G ⊆ γ(S, a)}.

This is the game version of CB21 Thm 5.3.

**Hardness.** From a deterministic TM T with:
* alphabet Σ = {○, ●};
* one halting state q_ω, start state q_0;
* input all ○ (constant input), head starting at 0 and staying in [0, 2^n);
* question: does T halt? This is EXPSPACE-hard for 2^n-space-bounded machines.

The construction builds P with Éloise wins G(P, (2n+4)r) ⇔ T halts after exactly r steps; Lemma 3 with m = 2n+4 then removes the non-multiples. **Time runs backwards:** the initial state says "T is halting", the goal says "T is starting".
* Main variables: d_0..d_{n−1} (a cell index c, written [c]), Σ, h ("head"), Q. Further auxiliary variables are "omitted" but there are linearly many.
* Invariant: after each full cycle exactly one variable of Σ ⊔ {h} ⊔ Q is true. Claims for all t, c:
  * **tape:** Éloise wins G(P_{[c]⊔{σ}}, (2n+4)t) ⇔ cell c holds σ at time t;
  * **head:** Éloise wins G(P_{[c]⊔{h}}, …) ⇔ the head is at c at time t;
  * **state:** Éloise wins G(P_{[c]⊔{q}}, …) ⇔ T is in q at time t;
  * Éloise must lose all of these if T halted before time t.
* One cycle (2n+4 turns) is one backward step:
  * **σ true.** Éloise adds h and picks either:
    * *Write*: replace σ by a σ′ and add a q ∈ Q \ {q_ω} such that T writes σ when reading σ′ in q; or
    * *Preserve*: Abélard deletes σ or h. If h survives, Éloise changes c to some c′ ≠ c by flipping at least one bit, over n+1 of her moves.
  * **h true.** Éloise adds σ and q ∈ Q \ {q_ω}. She increments c if T moves left on (σ, q), and decrements it if T moves right.
  * **q true.** Éloise deletes q, adds h, σ and q′ ∈ Q \ {q_ω} with δ(q′, σ) going to q, and chooses any c′ (2n+1 turns).
  * **Last move of the cycle:** Abélard deletes all of Σ ⊔ {h} ⊔ Q but one, i.e. he chooses which sub-claim to check.
* Initial state {q_ω} (and c = 0).
* Goal ○ ∨ q_0 ∨ (h ∧ ¬d_0 ∧ … ∧ ¬d_{n−1}). This is disjunctive with negative literals and is "compiled into STRIPS by creating several copies of all actions: ones that make the goal true and ones that make the goal false", which is vague.
* Correctness is by induction on t: the three claims, with case analysis on whether the head is at c.

**Pass variant.** The cycle is extended to 2n+6 turns. Add ✓ and a fact ⋆ required by all non-✓ actions, plus 2n+6 ⋆-consuming actions that set or reset the goal depending on the counter's parity. Then T halts after exactly r steps ⇔ Éloise wins G(P^✓, (2n+6)r + ε) for some (equivalently all) ε ∈ {−1, 0, 1}, and Éloise loses for 2 ≤ ε ≤ 2n+4.

**Even/odd restriction:** by Lemma 2.

**Gaps:** the STRIPS encoding of the cycle (auxiliary variables, turn counter positions, the "flip at least one bit" and increment/decrement gadgets, the goal compilation) is omitted. The pass variant is a sketch. A formalisation has to design these gadgets explicitly.

### 5.5 Thm 2 / Thm 3
Thm 2 = CB21 Thm 5.3. Thm 3 is inherited from H+23 (deterministic loop-unrolling undecidable; PCP → CFG → HTN).

### 5.6 Thm 5 — game → regular loop-unrolling FOND HTN
Start from P′ = (P′, A′, I′, G′) := Lemma 2-1(P), so that Éloise wins G(P, r) ⇔ Éloise wins G(P′, 2r). Assume w.l.o.g.:
* A′ has an action with a precondition (needed so that win∃ can be set temporarily);
* A′ has an action without preconditions (Lemma 1-3; Éloise's dummy move after a win).

**Variables of H:**
* v(p) and bu(p) for p ∈ P′;
* do(a) for a ∈ A′;
* done, win∃, bu∃.

**Primitive names:** for each a ∈ A′:
* Éloise(a) = (v[Π+], v[Π−] ⊔ {done}, {E_a}), where Π− is a negative precondition;
* Abélard(a) = ({do(a)}, ∅, {E_a});
* both with E_a = (v[E+] ⊔ {done}, v[E−] ⊔ {do(a)}). The paper writes E+ for v[E+], an abuse of notation.

**backup network** (Fig. 3; unordered, deterministic). For each p ∈ P′ two tasks:
* `v(p) → ¬bu(p), ¬v(p)`;
* `¬v(p) → bu(p), v(p)`.

Same for win∃/bu∃. Executing both tasks for p in the only possible order copies v(p) into bu(p) and leaves v(p) unchanged (they flip v(p) twice).

**restore network:** the same with v ↔ bu swapped (copies bu into v).

**cont network** (Fig. 4, read from the rendered PDF). Notation `pre → eff`; "thick" tasks come in |A′| copies. Upper half (Éloise's move):
* E0 = `done →` (precondition done, no effect) ≺ backup₁;
* backup₁ ≺ each thick editing task `→ ¬v(p)`, `→ v(p)` (all p), `→ ¬done`;
* Éloise(a) for every a ∈ A′: only ordered before restore₁;
* all editing tasks and all Éloise(a) ≺ restore₁;
* restore₁ ≺ X = `→ ¬done, do(a′)`, nondeterministic with |A′| outcomes (one per a′ ∈ A′: add do(a′), delete done). This is Abélard's choice.

Lower half (Abélard's move); X precedes all of:
* E1 = `done →` ≺ backup₂;
* Abélard(a) for all a;
* `do(a), ¬v(p′) → win∃` for each a and each positive precondition p′ of a;
* `do(a), v(p″) → win∃` for each a and each negative precondition p″ of a;
* `win∃ → done`.

Then:
* backup₂ ≺ editing tasks `→ do(a)` (all a), thick `→ v(p)`, thick `→ ¬v(p)`;
* all lower-half tasks ≺ restore₂;
* restore₂ ≺ Y = `→ ¬done, ¬do(a′) for all a′` ≺ comp.

**stop network:** two unordered tasks `v[G′] → win∃` and `win∃ → v[G′]`. Both can be executed iff G′ holds or win∃ holds.

**H:** t_0 = comp, S_0 = v[I′]. Regular (comp is last) and loop-unrolling (one compound, two methods).

**Mechanics:**
* done is false at the start of each copy, so exactly one Éloise(a) can run before E0. That is Éloise's move.
* backup / edit / restore lets the remaining Éloise(a′) run with no net effect (restore puts back v and win∃).
* X: nature picks a′.
* If a′ is inapplicable, the planner fires a check task, then win∃ and `win∃ → done`. win∃ survives restore because it was set *before* backup₂. Afterwards Éloise uses the precondition-free action.
* Otherwise Abélard(a′) is executed first (to get done), which applies a′. The remaining Abélard tasks and check tasks run on the edited state after backup₂ and are undone by restore₂. A check task fired then only sets win∃ temporarily, which restore₂ resets. Some check task must exist, which is why an action with a precondition is assumed.

**Claim:** Éloise wins G(P′, 2r) ⇔ H is solvable with exactly r cont applications.

**Gaps:** correctness is argued informally. The exact ordering is only in the figure (reproduced above). It must be checked that no interleaving of tasks from different blocks (e.g. Éloise(a) tasks unordered with backup₁, check tasks unordered with backup₂ during which v(p) is temporarily flipped) can be exploited. For Éloise tasks this is prevented by the done flag; for check tasks the danger only exists when win∃ is already true. "Enough (e.g. |A′|) copies" of the thick tasks must be made exact. **Uses negative preconditions throughout**, so with the CB formalism compile them away first (§1.1 item 2).

### 5.7 Thm 4 — regular loop-unrolling FOND HTN is EXPSPACE-hard
Thm 1 (with ✓, any parity; Lemma 2-1 inside Thm 5) + Thm 5: ∃r: Éloise wins ⇔ H solvable. With CB21 Thm 5.3 this makes **regular PO FM strong OD EXPSPACE-complete**. H's cont network is PO, consistent with TO regular being PSPACE.

### 5.8 Thm 6 — regular loop-unrolling FOND HTN → game
T_0, T_cont, T_stop are the primitive tasks of t_0, cont and stop, disjoint.
* **Variables:** H's variables plus do(t), done(t) for t ∈ T.
* **Actions for each t (name pr):**
  * t_Éloise: requires pre(pr), ¬done(t), ¬do(t′) for all t′, done(t′) for all t′ ≺ t. It also requires done[T_0] if t ∈ T_cont ⊔ T_stop, and done[T_cont] if t ∈ T_stop. Effect: add do(t).
  * For order-minimal t ∈ T_cont, t_Éloise^⟲: like t_Éloise, but it consumes done[T_cont] (instead of requiring ¬done(t)) and requires ¬done(t′) for t′ ∈ T_stop. This starts a new copy.
  * For each outcome e of pr, t^e_Abélard: consume do(t), add done(t) ⊔ E+, delete E−.
* **Initial state:** S_0 ⊔ done[T_cont]. **Goal:** done[T].
* **Claim:** Éloise wins G(P, 2(|T_0| + r|T_cont| + |T_stop|)) ⇔ H solvable with r cont applications.

**Gaps:** edge cases are not treated (|M| < 2, primitive t_0, empty T_cont). Uses negative preconditions. Not needed for any table cell (membership is given by Thm 2), but it shows the equivalence.

---

## 6. IDEAS file, idea by idea

### 6.1 PCP: tail-recursive PO FM strong OD is undecidable (conjecture)
**Construction sketch:**
* tn_I = init ≺ {C_1, C_2}, with C_1 and C_2 unordered compound tasks. TR allows this because TR only restricts methods.
* C_k has, for each PCP index i, a regular method "tasks spelling word w_i^{(k)}, then C_k", plus a stop method.
* init is nondeterministic with outcomes "character mode" and "word mode".
  * Character mode: the policy checks that the two primitive chains spell the same string.
  * Word mode: it checks that the index sequences agree.
* FM forces one decomposition, chosen before the mode is revealed, to pass both checks, i.e. a PCP solution.

**Gaps / open points:**
* (a) The synchronisation gadgets are not given. Each side is a chain; interleave them alternately with token facts ("pending x").
* (b) **Making one mode's check vacuous in the other mode is non-trivial with positive preconditions and unconditional effects.** Task names are fixed before the mode is known, deleting token facts breaks vacuity, and "skip" tasks with a mode precondition deadlock when they sit inside the chains. A concrete gadget must be designed; negative preconditions or an escape fact (as in CB21 5.1's `clear`) may help.
* (c) PCP needs a non-empty index sequence: force at least one non-stop method.
* (d) The lengths of the two strings differ per index, so word mode must compare index tokens, not tasks.
* (e) Tail-recursiveness of the final construction must be checked against the definition (G3).

If it works, it fills CB21's TR/PO/strong OD cell (undecidable; semi-decidable by Thm 3.1).

### 6.2 Counters: acyclic EXPSPACE-hard, TR 2-EXPTIME-hard (conjecture)
**Starting point:** a re-reading of ABA15 Thm 6.1. Simulate a TM with 2^n cells and alphabet {0, 1}, starting with all 0s. There is a goal state and no halting state. The question is whether a goal state is ever reached.
* **Network:** a disjoint union of one *control* network, many *0-cells* and many *1-cells*.
* **Three time levels:** global step ⊃ 2^n atomic steps ⊃ 2^n subatomic steps.
* **Cells:**
  * every cell is a chain implementing a clock to 2^n (atomic speed);
  * a cell must be initialised, and after each initialisation or increment it pauses until it is resumed;
  * the clock value lives in the *position within the cell's chain*, not in facts;
  * the cell's last task is "finalise".
* **Control:** two clocks (atomic and subatomic); TM state and head position are kept in facts. Everything is acyclic (doubling) with one method per compound task, using a "backup and trash" gadget (DB24/DB25) to merge alternative methods.
* **Phase 1 (initialise the tape):** for each atomic step a:
  * increment a already-initialised cells;
  * resume a cells;
  * initialise a new 0-cell.
* **Phase 2 (each global step):** for each atomic step:
  * find the unique cell whose clock is at 2^n − 1, read its symbol σ, and finalise it;
  * if the atomic clock equals the head position, apply the transition and initialise a σ′-cell; otherwise initialise a σ-cell;
  * do 2^n − 1 increments and 2^n resumes of some cells.
* **Size:** 2^{2n} 0-cells and 2^{2n} 1-cells suffice for 2^n global steps (acyclic).
* **TR variant:** three compound names (control, 0-cell supply, 1-cell supply) get stop/continue methods; the rest have one method.
* When the goal is reached, a flag enables "cheat" tasks that execute everything else.
* **Deterministic result:** acyclic is NEXPTIME-hard, TR is EXPSPACE-hard (ABA15 Thm 6.1).
* **With nondeterminism** (ATM ∀ via action outcomes): acyclic AEXPTIME = EXPSPACE, TR AEXPSPACE = 2-EXPTIME.
* Claimed to work for FM strong OD, MP strong and MP strong cyclic. In the acyclic case each compound has one method, so FM = MP. In the TR case the only method choice is "how many global steps", and more is never harmful.
* For strong cyclic TR: make the objective "never reach the goal" (complement, since AEXPSPACE = 2-EXPTIME is closed under complement) and let the plan add time forever.

**Gaps:**
* (a) The TM in the sketch is deterministic, but NEXPTIME/AEXPTIME hardness needs nondeterministic/alternating choice. Where ∃ choices (planner orderings) and ∀ choices (outcomes) enter is not specified.
* (b) The cell / clock / pause / resume gadgets, the "find the unique cell" precondition mechanism, and the "backup and trash" merge are not spelled out.
* (c) The strong-cyclic argument relies on CB22's literal Def 7, where infinite executions without terminal nodes are allowed vacuously (G6). Under the standard Cimatti semantics (goal reachable from every reachable node) it does not obviously work.
* (d) Wrong cross-reference: "Theorem 4.5 from the 2022 paper" should be **CB22 Thm 2**. CB22 has no Thm 4.5; CB21 Cor 4.5 is regular weak.
* (e) For FM, "it can never hurt to add more global time steps" must be argued under FM. In FM, the number of steps is fixed before execution and therefore before the ∀ outcomes are known, and this choice must suffice for *all* branches of the ATM tree. It does, if the ATM is assumed to halt within a uniform bound, e.g. by a counter.

### 6.3 Total order, membership: MP strong (and strong cyclic) TO arbitrary in 2-EXPTIME
**Algorithm.** The table T consists of triples (c, s, S′) with c ∈ N_C, s ⊆ P, ∅ ≠ S′ ⊆ 2^P. Meaning: from state s, the planner can execute (fully refine and run) a task c so that the set of possible end states is exactly S′. Least fixed point; repeat while T grows. For every (c, s, S′) and every method μ of c with network τ = u_1…u_ℓ (TO), containing n compound positions:
* For every tuple (f_1, …, f_n) of partial functions f_i : 2^P → 2^{2^P} \ {∅} such that (c_i, s′, f_i(s′)) ∈ T for all s′ ∈ dom(f_i):
  * replace the i-th compound task by an artificial nondeterministic primitive task with precondition "s′ ∈ dom(f_i)" and outcome set f_i(s′);
  * expand the state tree of the resulting primitive chain from s;
  * if no precondition is violated and the set of leaf states equals S′, add (c, s, S′).
* n = 0 is allowed; this is the base case.

Answer: ∃S′ ≠ ∅ with (c_0, s_0, S′) ∈ T, after making tn_I a single compound task c_0 w.l.o.g. (a new compound with one method; this keeps TO).

**Complexity:**
* #triples ≤ |N_C| · 2^{|P|} · 2^{2^{|P|}};
* #tuples ≤ (2^{2^{|P|}})^{n·2^{|P|}};
* the state tree has depth ≤ ℓ and branching ≤ 2^{|P|};
* at most #triples iterations.

All doubly exponential, so 2-EXPTIME.

**Proof obligations not in the sketch:**
* (a) Soundness: build an MP policy from derivations. CB22 requires a positional policy on (tn, s) whose execution structure is **acyclic**. Use a rank (derivation stage) and always choose a rank-decreasing derivation, an attractor argument, to avoid revisiting (tn, s).
* (b) Completeness: from a strong policy, extract triples by well-founded induction on the finite acyclic execution structure. One f_i per state is enough because in TO the remaining suffix is identical for all branches reaching compound position i in state s′.
* (c) The precise meaning of "exactly S′" versus "⊆ S′": exact sets are what the algorithm computes. Upward closure is not needed for the final check, but it simplifies proofs.
* (d) It needs the MP-progression lemma (G8).

**Strong cyclic variant:** greatest fixed point starting from all triples, allowing S′ = ∅ for "never finishes". The author says it is "not exactly correct yet". It also depends on the strong-cyclic definition (G6). Treat it as open.

### 6.4 Total order, hardness: MP strong TO arbitrary is 2-EXPTIME-hard
**Source:** a deterministic TM with a run of length < 2^{2^n} and tape cells < 2^{2^n}, one halting state q_h. 2-EXPTIME-hardness needs a machine running in doubly exponential time.

**Facts (linearly many):**
* CHECK_i, CHOICE_i (i < n);
* SYMBOL_σ, INTSTATE_q;
* TIME, TIMEVERIFY, HEAD, HEADVERIFY, HEADNEW, TAPE, TAPEVERIFY;
* MACHMODE, TAPEMODE.

**Setup:** initial state {INTSTATE_{q_0}}; tn_I = ⟨advance⟩; [assert INTSTATE_{q_h}].

**Key idea.** CHECK (an n-bit number "Check" < 2^n) is set nondeterministically, i.e. adversarially, in the base case of the recursion. Execution order makes that base case the *first* executed step. So the planner must commit to the whole witness for *every* bit position Check of the doubly-exponential numbers t, C. A number < 2^{2^n} is "encoded into the task network" as a sequence of addmaybe(V)/delmaybe(V) tasks, one per digit position d (CHOICE runs through d via `inc`). Each sets V iff d = Check, so afterwards V = digit_Check of the number.

**Claims:**
* **Tape:** cell C holds σ at time t ⇔ the planner can execute ⟨advance⟩ from the initial state guaranteeing SYMBOL_σ, TAPE ↔ digit_Check(C), TIME ↔ digit_Check(t).
* **Machine:** the TM is in q with head at C at time t ⇔ the same guarantee with INTSTATE_q, HEAD ↔ digit_Check(C), TIME ↔ digit_Check(t).

**Methods** (the list in IDEAS is the specification):
* advance:
  * base: perhaps-add each CHECK_i, then choose(TAPE);
  * two "preserve" methods per σ;
  * "transitionright" / "transitionleft" methods per transition (σ, q) → (σ′, q′, dir).
* advanceandclock, advanceandcarryover: binary increment of t with carry over digits.
* advanceinmode: nature chooses TAPEMODE/MACHMODE, then the recursive ⟨advance⟩ for t − 1.
* preserve / transition: left-recursive builders of the digit sequences.
* Gadgets: preserveverify, transitionverify, transition{left,right}, transitionandcarryover{left,right}, asserteq, choose, copy, get, let, goto, inc.

The grammar is left-recursive (⟨preserve⟩ → ⟨preserve⟩; ⟨inc⟩). That is fine for TO arbitrary but not TR. All digit decisions for step t are fixed (as a suffix) before the mode outcome and before the recursive call is refined; MP lets the planner choose the method for the inner ⟨advance⟩ after the mode is revealed.

**Gaps:**
* (a) **Undefined compound tasks:** ⟨assertmaybe(V)⟩ and ⟨forbidmaybe(V)⟩ are used (advanceandclock, advanceandcarryover, transitionleft/right, transitionandcarryover*) but never defined. They are presumably like addmaybe/delmaybe with an assert/forbid of V at digit Check.
* (b) **Base case for Tape is wrong as written:** at t = 0 the Tape claim needs SYMBOL_blank, but the initial state is only {INTSTATE_{q_0}} and the base method does not add SYMBOL_blank.
* (c) The inductive step is missing ("we have to distinguish cases…").
* (d) Uses negative preconditions ("forbid").
* (e) It is not argued that the planner cannot gain from encoding an inconsistent number (e.g. a different t on different digits). This is presumably prevented because Check is universal, but the argument is needed.
* (f) The relation of the halting time to the < 2^{2^n} bound, and the final [assert INTSTATE_{q_h}], need care: the machine must halt within 2^{2^n} steps, and its time counter must not overflow.

---

## 7. Gaps, errors and vague steps (consolidated)

**Definitions**
* **G1 (CB21 Def 3.4, CB22 Def 10).** "Stratification is a total order", yet strata are sets with x ≤ y ∧ y ≤ x. It must be a total **preorder**.
* **G2 (CB21 Def 3.5, CB22 Def 11, acyclic).**
  * "c ≤ c′ if … α(c′) ∈ T" is a typo for "∃t ∈ T: α(t) = c′".
  * "if c ≤ c′ then c′ ≰ c" contradicts reflexivity.
  * The orientation (parent ≤ child) is opposite to the TR definition (child ≤ parent).

  Use "the decomposition graph is acyclic".
* **G3 (TR, CB21 Def 3.6, CB22 Def 12).** "If there exists a last compound task t" is ambiguous: last *task* (all others precede it, the ABA15 meaning) or last *among compound tasks*? Lemma 4.3's claim that TR is preserved only holds under the ABA15 reading. Example: under the other reading, a method c → [c′, a] with c′ on c's stratum becomes c → [c′, c_a], which violates TR. Fix the ABA15 reading. Also only methods are restricted, not tn_I.
* **G4 (CB21 Defs 2.9–2.11).** The execution structure uses "S is executable by T′", which is not tied to the actual policy history, and R ⊆ S × T × S forgets the executed set. Execution sequences are *all* finite sequences in R, so they include prefixes. Read literally, "every execution sequence is complete" fails for every n ≥ 2 because the length-1 prefix is incomplete. Formalise strong/weak OD by the recursive solvability of §1.2 (= DB25), and prove a lemma relating it to policies π : 2^T × S → T.
* **G5 (CB22 Def 5).**
  * The policy may pick *any* task t, not necessarily a first one. A ≺-minimality requirement is missing; Alg. 1, Alg. 2 and graph search all assume it.
  * A primitive t may be non-executable in s. Then γ is undefined and Def 6 yields a terminal non-goal node; this should be stated.
* **G6 (CB22 Def 7, strong cyclic).** "Every terminal node is a goal node" with no fairness or reachability condition. An infinite L without terminal nodes (e.g. a policy repeatedly applying a recursive method c → [c]) is vacuously strong cyclic. The intended (Cimatti 2003) definition: every node of L can reach a goal node. Several claims depend on the fix:
  * Thm 3 hardness (strong cyclic ↔ FOND strong cyclic);
  * Thm 5 strong-cyclic EXPSPACE-hardness (deterministic special case);
  * IDEAS' strong-cyclic TR argument, which on the contrary *relies on* the literal version.
* **G7 (CB22, Alg. 2 for strong cyclic).** "Remove V" turns cycles into non-terminating branches, which an ATM rejects. That computes strong, not strong cyclic. Strong-cyclic membership is only justified by the graph search (Thms 3–5).
* **G8 (CB22 Defs 5–6 vs. Alg. 2 / graph search).** Policies may decompose any compound task, but the algorithms and the ABA15 size bounds decompose only first tasks (progression). A lemma "delaying a decomposition until the task is first never hurts (MP strong / strong cyclic / weak)" is needed and not stated. It is plausible: later decisions have more information.

**Proof errors and sketches, CB21**
* **G9 (CB21 Thm 5.1 hardness — errors).**
  * (i) pre(turn_i) = {¬x_i} lets P1 play onto an O-square. Then x_i ∧ o_i, illegal_i fires, C holds and `clear` makes everything executable, so P1 always "wins" after P2's first reply. Fix: pre(turn_i) ⊇ {¬o_i}.
  * (ii) fin_turn_i may be played at any time and gives P1 an un-answered extra move mid-game. Fix: require R also in turn_i, so that fin_turn really is the last move.
  * (iii) win_λ adds x_j for all j, so illegal_j becomes executable for every O-square and the not_lose check (P2 has no line) can be bypassed. Fix, e.g.: illegal_i additionally requires R; fin_turn adds a fresh fact Fin required by win_λ.
  * (iv) P2 "passing" (playing on its own O-square) needs the standard "an extra stone never hurts" argument, which is not given.
  * (v) |L| ≤ 4mn (two diagonal directions), not 3mn, so the task count is also off.
  * (vi) The cited PSPACE-completeness of (m, n, k)-games for fixed k ≥ 4 (Hsieh & Tsai, p = q = 1) should be double-checked. Reisch's Gomoku result is for k = 5 with board-size input.

  Recommendation: re-prove PSPACE-hardness of PO primitive strong OD from TQBF or from fixed-length planning games, or carefully repair the (m, n, k) reduction. Cor 1 of CB22 inherits this.
* **G10 (CB21 Lemma 4.6 proof).** The written argument is only one direction plus an unclear induction. Use the invariant s′_i = ⋂S_i (§3.11). It needs the add/del normalisation and positive preconditions.
* **G11 (CB22 Thm 1 hardness).** No acceptance check, so the planner can decompose every 1·sim into tn_∅ and "win" trivially. A final task requiring an accepting configuration is needed, along with details of the precondition coupling. Outline only.
* **G12 (CB22 Thm 2 / Thm 5 hardness).** "Extend ABA15 Thm 6.1 / the TR EXPSPACE proof to ATMs" is an outline only. The assumption that "universal transitions all move in the same direction" and its compilation are not detailed. Formalisation needs ABA15's constructions in full; alternatively use IDEAS counters, which are equally unfinished.
* **G13 (CB21 Cor 4.5).** The membership argument via the compiled (non-regular) problem is vague. Use direct nondeterministic progression with outcome guessing (§3.10).
* **G14 (CB21 Thm 5.3).**
  * "For all s ∈ A" should be S_A.
  * Prop 2.16 is stated for start state s_I but used for arbitrary s.
  * The block-decomposition correctness ("equivalence relation induced by compound tasks being last") is only sketched.
* **G15 (CB21 Prop 2.12 proof).** Off-by-one in the policy indices; T_i should be the set of tasks executed before t_i.
* **G16 (CB22 Thm 4/5 counting).** The index typos i^n vs n^i are harmless. The isomorphism-testing cost is folded in loosely; fine for upper bounds.
* **G17 (CB22 Thm 3 hardness).**
  * The method repeat → [done] is not mentioned.
  * The source problem's fragment (positive preconditions, conjunctive goal, explicit nondeterministic effects) must match a known EXPTIME-hardness result.
  * Strong cyclic needs G6 fixed.
* **G18 (CB22 Prop 2).** The positional/isomorphism condition on MP policies requires choosing a repetition-free trace; this is unstated.

**Proof sketches and errors, DB25**
* **G19 (DB25 Thm 1 hardness).**
  * The STRIPS realisation of the cycle (turn counter positions, "flip ≥ 1 bit", increment/decrement over n+1 Éloise moves, Abélard's "delete all but one") is omitted.
  * The disjunctive goal compilation is vague.
  * The pass variant is a sketch.
  * The assumptions on T (one halting state, head stays in [0, 2^n), left-end behaviour, and halting being EXPSPACE-hard for such T) are standard but must be fixed precisely.
* **G20 (DB25 Lemma 1, Lemma 2).** The game equivalences are argued informally.
* **G21 (DB25 Thm 5).**
  * Correctness of the backup/restore gadget under arbitrary interleavings is informal.
  * "Enough copies" of the thick tasks is not exact.
  * Abuse of notation: E+ for v[E+], do(a) for {do(a)}.
  * Negative preconditions are used.
* **G22 (DB25 Thm 6).** Edge cases (|M| < 2, primitive t_0, empty T_cont) are not handled.

**IDEAS**
* **G23.** PCP gadget (vacuity across modes) missing (§6.1).
* **G24.** Counters: deterministic TM vs. needed alternation; gadgets unspecified; strong-cyclic argument depends on G6; wrong reference "Thm 4.5 (2022)" → CB22 Thm 2 (§6.2).
* **G25.** TO membership: soundness needs an acyclic positional policy (rank argument); strong cyclic variant unfinished (§6.3).
* **G26.** TO hardness: assertmaybe/forbidmaybe undefined; Tape base case lacks SYMBOL_blank; inductive step missing; negative preconditions (§6.4).

---

## 8. Dependencies

### 8.1 External (deterministic / classical) results used as black boxes

| Used result | Used by |
|---|---|
| SAT NP-hard (Cook) | CB21 4.1 |
| FOD PO primitive NP-c (EHN96) | CB21 4.2 (alt. hardness), 4.7 |
| FOD regular PSPACE-c (EHN96), progression algorithm and STRIPS encoding | CB21 4.5, 4.7; CB22 Thm 3 hardness pattern |
| FOD acyclic TO PSPACE-c / PO NEXPTIME-c; TR TO PSPACE-c / PO EXPSPACE-c; arb TO EXPTIME-c (ABA15) | CB21 4.4, 4.7, 4.8; CB22 Thm 5 (strong cyclic hardness); 5.2 lower bound |
| FOD arb PO undecidable (EHN96, GB11) | CB21 3.1; CB22 caption |
| ABA15 Lemma 3.6 (TO TR progression size k + r·h) | CB22 Thm 1, Thm 4 |
| ABA15 Lemma 3.4 (PO TR progression size k·r^h) | CB22 Thm 5 |
| ABA15 Cor 3.2 (acyclic decomposition size bound) | CB21 5.2 (cited as "Cor 3.2" in the table discussion), CB22 Thm 2 |
| ABA15 §4 doubling construction | CB22 Thm 1 hardness |
| ABA15 Thm 6.1 (NTM / TM via counters) | CB22 Thm 2, Thm 5 hardness; IDEAS counters |
| Bylander 1994 encoding | CB22 Thm 1 hardness |
| FOND strong / strong cyclic EXPTIME-c (Rintanen 2004) | CB22 Thm 3 hardness |
| Cimatti et al. 2003 graph algorithms (poly in explicit graph) | CB22 Thms 3, 4, 5 membership |
| AP = PSPACE, APSPACE = EXPTIME, AEXPTIME = EXPSPACE, AEXPSPACE = 2-EXPTIME | CB21 5.1; CB22 Thms 1, 2, 5; IDEAS |
| Savitch | CB21 4.5, 5.2, 5.3; DB25 Thm 1 |
| (m, n, k)-game PSPACE-c (Reisch; Hsieh & Tsai) | CB21 5.1 hardness |
| EXPSPACE-hardness of halting for 2^n-space DTM | DB25 Thm 1 |
| PCP undecidable; deterministic loop-unrolling undecidable (H+23) | DB25 Thm 3; IDEAS PCP |
| Compilation of negative preconditions (Gazen & Knoblock) | DB25 (implicitly every construction); IDEAS |

### 8.2 Internal dependency graph

```
CB21
  Prop 2.12 (weak LD = weak OD) ──► all weak cells
  Prop 2.13 (strong LD ⇒ strong OD)
  Prop 2.15 (TO: strong LD = strong OD) ──► Cor 4.8
  Prop 2.16 (verify policy in P) ──► Thm 5.3
  Thm 3.1  ◄── FOD undecidability (EHN96/GB11); semi-dec uses Cor 4.2 / Thm 4.7 / Thm 5.1
  Thm 4.1  ◄── SAT
  Cor 4.2  ◄── Thm 4.1 (hardness), guess&check
  Lemma 4.3 ──► Thm 4.4 ◄── ABA15/EHN96 FOD bounds
  Cor 4.5  ◄── EHN96 progression (+ Lemma 4.3 idea)
  Lemma 4.6 ──► Thm 4.7 ◄── all FOD bounds
  Thm 4.7 + Prop 2.15 ──► Cor 4.8
  Thm 5.1  ◄── AP=PSPACE, (m,n,k)-game   [hardness proof broken: G9]
  Thm 5.2  ◄── Thm 5.1 + size bound + Savitch
  Thm 5.3  ◄── Prop 2.16, regular block structure, Savitch

CB22
  Prop 1 ──► Cor 1 ◄── CB21 Thm 5.1, CB21 Cor 4.8
  Prop 2 ──► weak column ◄── CB21 Thms 4.1, 4.2 (Cor), 4.4, Cor 4.5
  Alg 2 ──► Thm 1 (memb) ◄── ABA15 L3.6, APSPACE=EXPTIME;   Thm 1 (hard) ◄── ATM, Bylander, ABA15 §4
  Alg 2 ──► Thm 2 (memb) ◄── ABA15 Cor3.2, AEXPTIME=EXPSPACE; Thm 2 (hard) ◄── ABA15 Thm 6.1 + ATM
  Graph search ──► Thm 3 (memb) ;  Thm 3 (hard) ◄── Rintanen 2004, EHN96 encoding
  Graph search ──► Thm 4 (memb) ◄── ABA15 L3.6;  Thm 4 (hard) ◄── Thm 3
  Graph search ──► Thm 5 (memb) ◄── ABA15 L3.4;  Thm 5 (hard) ◄── ABA15 TR EXPSPACE (+ ATM ext.)
  (all MP algorithms) ◄── G8 (progression lemma)

DB25
  Lemma 1, Lemma 2, Lemma 3 ──► Thm 1 (hardness; ✓ and parity variants)
  CB21 Thm 5.3 ──► Alg 1 (Thm 1 membership) and Thm 2
  H+23 ──► Thm 3
  Lemma 2-1, Lemma 1 ──► Thm 5
  Thm 1 + Thm 5 ──► Thm 4  ──► (with CB21 5.3) regular PO FM strong OD EXPSPACE-complete
  Thm 6 (converse, independent)

IDEAS
  PCP ──► FM TR PO strong OD undecidable (fills CB21 cell; uses CB21 Thm 3.1 for semi-dec)
  Counters ◄── ABA15 Thm 6.1, DB24/DB25 backup-and-trash
           ──► FM acyc PO EXPSPACE-hard (with CB21 5.2: complete)
           ──► MP strong cyclic TR PO 2-EXPTIME-hard (with CB22 Thm 5: complete) [depends on G6]
  TO membership ◄── G8 ──► MP strong TO arb ∈ 2-EXPTIME
  TO hardness  ──► MP strong TO arb 2-EXPTIME-hard
```

### 8.3 Suggested formalisation order (minimal path to the tables)
1. Core syntax (§1.1) and semantics:
   * FM weak/strong LD;
   * FM strong/weak OD as recursive solvability (§1.2);
   * MP via progression least fixed point (§1.3).

   Prove the equivalence lemmas: Props 2.12, 2.13, 2.15; CB22 Props 1, 2; the MP progression lemma G8.
2. Compilations: Lemma 4.3 and Lemma 4.6 (invariant s′ = ⋂S). Prove that they preserve classes, plus the negative-precondition compilation.
3. "Same as FOD" results: Thms 4.4 and 4.7, Cor 4.8, with FOD results as axioms.
4. Direct results:
   * Thm 4.1 (SAT reduction, fully specified);
   * Thm 5.1 membership;
   * Thm 5.1 hardness, repaired or replaced (G9).
5. Regular FM: Thm 5.3 membership; DB25 Thms 5 + 1 for hardness. This is the largest construction; DB25 Thm 1's STRIPS gadgets must be designed.
6. MP: graph search (Thms 3–5 membership), Thm 3 hardness from FOND planning (axiom), Thm 4 hardness.
7. Open items: IDEAS conjectures.
