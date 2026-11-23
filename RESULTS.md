# Complexity of FOND HTN plan existence: overview

Rows are fragments (TO = totally ordered, PO = partially ordered); columns are solution
notions: *fixed* methods [CB21] and *flexible* method-based policies (MP) [CB22]. "-c" means
complete.

| Mark | Meaning |
|---|---|
| ✅ | formalised in Lean, both bounds unless the cell says otherwise |
| (P) | paper result only, not formalised |
| ⏳ | formalisation in progress |
| (W) | the published proof is **wrong**: it proves a false step or the construction admits a trivial or wrong solution. The Lean proof uses a repaired or new construction |
| (I) | the published proof is **incomplete**: an outline or sketch with missing gadgets or steps. The Lean proof fills the gaps, or uses a new construction |

`G…` refers to the numbered gap list in `doc/results_catalogue.md` §7.

Sources:

* [CB21] Chen & Bercher, ICAPS 2021 (fixed methods)
* [CB22] Chen & Bercher, ICAPS 2022 (method-based policies)
* [DB25] Dekker & Behnke, ICAPS 2025
* [D26] the ideas file (`doc/ideas_for_pascal_spring_2025.md`)
* "inh." means the bound is inherited from deterministic HTN planning (Erol et al.; Alford et al.)

| Fragment | Fixed: weak (LD = OD) | Fixed: strong LD | Fixed: strong OD | MP: weak | MP: strong | MP: strong cyclic (fair) |
|---|---|---|---|---|---|---|
| primitive, TO | NP-c ✅ [CB21 Thm 4.1] | in P ✅ [CB21 Cor 4.8] | in P ✅ [CB21 Cor 4.8] | NP-c ✅ [CB22 Prop 2] | in P ✅ [CB22 Cor 1] | in P ✅ [CB22 Cor 1] |
| primitive, PO | NP-c ✅ [CB21 Cor 4.2] | NP-c ✅ [CB21 Thm 4.7] | PSPACE-c ✅ [CB21 Thm 5.1]; hardness (W) (G9), re-proved from TQBF | NP-c ✅ [CB22 Prop 2] | PSPACE-c ✅: membership [CB22 Cor 1]; hardness [CB22 Cor 1] inherits (W) from CB21 Thm 5.1, re-proved from TQBF | PSPACE-c ✅ [CB22 Cor 1]; as for strong |
| acyclic, TO | PSPACE-c ✅ [CB21 Thm 4.4] | PSPACE-c ✅ [CB21 Cor 4.8] | PSPACE-c ✅ [CB21 Cor 4.8] | PSPACE-c ✅ [CB22 Prop 2] | EXPTIME-c ✅ [CB22 Thm 1]; hardness (W) (G11: no acceptance check), new reduction | EXPTIME-c ✅ [CB22 Thm 1]; hardness (W) as for strong |
| acyclic, PO | NEXPTIME-c ✅ [CB21 Thm 4.4] | NEXPTIME-c ✅ [CB21 Thm 4.7] | EXPSPACE-c ✅: membership [CB21 Thm 5.2]; hardness [D26] counters (I) (G24), new construction | NEXPTIME-c ✅ [CB22 Prop 2] | EXPSPACE-c ✅ [CB22 Thm 2]; hardness (I) (G12), by the [D26] construction | EXPSPACE-c ✅ [CB22 Thm 2] / [D26]; hardness (I) |
| regular, TO | PSPACE-c ✅ [CB21 Cor 4.5]; membership (I) (G13) | PSPACE-c ✅ [CB21 Cor 4.8] | PSPACE-c ✅ [CB21 Cor 4.8] | PSPACE-c ✅ [CB22 Prop 2] | EXPTIME-c ✅ [CB22 Thm 3]; hardness (I) (G17) | EXPTIME-c ✅ [CB22 Thm 3]; hardness (W) (G6: literal definition), fair version needs a round counter |
| regular, PO, tn_I regular (CB21/Erol) | PSPACE-c ✅ [CB21 Cor 4.5]; membership (I) (G13) | PSPACE-c ✅ [CB21 Thm 4.7] | EXPSPACE-c ✅: membership [CB21 Thm 5.3] (I) (G14); hardness [DB25 Thm 4] (I) (G19–21) | PSPACE-c ✅ [CB22 Prop 2] | EXPTIME-c ✅ [CB22 Thm 3]; hardness (I) (G17) | EXPTIME-c ✅ [CB22 Thm 3]; hardness (W) (G6) |
| regular, PO, tn_I arbitrary (Bercher) | PSPACE-c ✅ | PSPACE-c ✅ | **undecidable** ✅ [D26] PCP (I) (G23), repaired with gated cheat tasks | PSPACE-c ✅ | EXPTIME-c ✅ | EXPTIME-c ✅ |
| tail-recursive, TO | PSPACE-c ✅ [CB21 Thm 4.4] | PSPACE-c ✅ [CB21 Cor 4.8] | PSPACE-c ✅ [CB21 Cor 4.8] | PSPACE-c ✅ [CB22 Prop 2] | EXPTIME-c ✅ [CB22 Thm 4] | EXPTIME-c ✅ [CB22 Thm 4] |
| tail-recursive, PO | EXPSPACE-c ✅ [CB21 Thm 4.4] | EXPSPACE-c ✅ [CB21 Thm 4.7] | **undecidable** ✅ [D26] PCP (I) (G23); semi-decidable [CB21 Thm 3.1] | EXPSPACE-c ✅ [CB22 Prop 2] | 2-EXPTIME-c ✅: membership [CB22 Thm 5]; hardness [CB22 Thm 5] (I) (G12), proved by the [D26] construction (counters, tableau transducer) | 2-EXPTIME-c ✅: membership [CB22 Thm 5]; hardness [CB22 Thm 5] (I) (G12), proved by the [D26] construction (same reduction as strong; safe-game soundness) |
| arbitrary, TO | EXPTIME-c ✅ [CB21 Thm 4.4] | EXPTIME-c ✅ [CB21 Cor 4.8] | EXPTIME-c ✅ [CB21 Cor 4.8] | EXPTIME-c ✅ [CB22 Prop 2] | **2-EXPTIME-c** ✅ [D26]; membership (I) (G25), hardness (I) (G26), new hardness construction | **2-EXPTIME-c** ✅: membership [D26] (W) for the fair reading (the sketched summary game is wrong), corrected [DBC26]; hardness [DBC26]: the strong construction is sound for fair policies |
| arbitrary, PO | semi-decidable and undecidable ✅ [CB21 Thm 3.1] | semi-decidable and undecidable ✅ [CB21 Thm 3.1] | semi-decidable and undecidable ✅ [CB21 Thm 3.1] | semi-decidable and undecidable ✅ | semi-decidable and undecidable ✅ (semi-decidability not stated in [CB22]) | **neither RE nor co-RE** ✅ [DBC26]: not semi-decidable (two-stack machines with stop ticks); complement not semi-decidable (Thm 4.1.1 reduction, inh.). **Σ¹₁-complete**: membership ✅ [DBC26] (Kleene normal form); hardness: recurrence of two-stack machines reduces ✅ [DBC26], Σ¹₁-completeness of recurrence [Harel 1986] cited, not formalised |

## Notes

* **Regular rows.**
  * [CB21] defines "regular" with a regular initial task network (`REGtn`).
  * Bercher et al.'s variant allows an arbitrary `tn_I` (`REG`).
  * The two classes differ only for strong OD: EXPSPACE-complete for `REGtn`, undecidable for `REG`.
* **Strong cyclic.**
  * The literal definition in [CB22] is wrong (G6): a policy that loops forever counts as a solution.
  * It also does not collapse to plan existence on deterministic recursive problems.
  * The Lean results therefore use the *fair* reading. On acyclic problems, fair coincides with strong.
* **Column-wide gaps, not marked per cell:**
  * Strong LD membership rests on the compilation of [CB21 Lemma 4.6] (I) (G10), which also had to be extended to negative preconditions.
  * MP rests on [CB22 Prop 2] (I) (G18) and on the unstated delay lemma (I) (G8).
  * The solution definitions of [CB21] and [CB22] (G4, G5) are themselves defective as written.
* **Further cells, all formalised:**
  * REG ∩ ACYC ∩ TO: NP-c.
  * DB25 Thm 1 (chosen-length games EXPSPACE-c): (P), (I) (G19). It is not needed, because DB25 Thm 4 is proved directly from machines.
* Detailed pointers to the Lean theorems: `STATUS.md`. Deviations from the papers: `modifications/main.tex`.
