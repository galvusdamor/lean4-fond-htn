import HtnComplexity.AcVerify.Tables
/-!
# The verifier of path witnesses

`HTN.Syn.AcVer.acV [x, a, w]` reads the code `x = instSer q` of an instance, the advice
`a = advOf d` of a domain description and a certificate `w`, the serialised list of the contents
of the entries of a path witness, and checks:

* `parseB` — every content parses into its six parts;
* `recsB` — the records of every entry form a well-formed path (`EntryOK`): the first record is
  a root step of the instance (`rootRecB`), the others are method steps (or, last in an empty
  leaf, a dummy step), consecutive records are linked (`linkB`), and the last record fits the
  flag (`lastB`);
* `childB` — every task of every expanded method is the next step of some entry (`ChildrenOK`);
* `rootsB` — every task of the initial task network starts some entry (`RootsOK`);
* `pairsB` — any two entries diverge at a step of the same network, in an order compatible with
  the ordering constraints (`PairOK`);
* `execB` — the states of the entries form a run of the actions of the action leaves from the
  initial state to a goal state (`ExecOK`).

All tests are predicates of Cobham's class (`HTN.Syn.AcVer.cobhamB_acV`).
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space

/-- The suffix after an entry is the end of its list. -/
def isLast (rest : List Bool) : Bool := !(rest.headD true)

/-- The suffix after an entry starts another entry. -/
def hasNext (rest : List Bool) : Bool := rest.headD false

/-- **The record `R` is the record of a root step of the instance `x`.** -/
def rootRecB (x R : List Bool) : Bool :=
  x.tails.any fun s => idPos x s &&
    decide (R = true :: (key 0 ++ (dbl (nvAt s) ++ (kat 2 R ++ (kat 3 R ++ [false]))))) &&
    isBDs (kat 3 R) &&
    ((decide (kat 2 R = key 0) &&
        (lblB (false :: undbl (kat 3 R)) x s || (decide (kat 3 R = key 0) && !lblB [] x s))) ||
      (decide (kat 2 R = key 1) && lblB (true :: undbl (kat 3 R)) x s))

/-- **The step of `Ry` decomposes the compound task of `Rx`**, by the table of heads. -/
def linkB (a Rx Ry : List Bool) : Bool :=
  decide (kat 2 Rx = key 1) && occB (tH a) (true :: (kat 0 Ry ++ (kat 3 Rx ++ [false])))

/-- **The last record fits the flag.** -/
def lastB (a c pre R : List Bool) : Bool :=
  (flagOf c || decide (kat 2 R = key 0)) && (!flagOf c || (!decide (pre = []) && occB (tD a) R))

/-- **The records of the content `c` form a well-formed path.** -/
def recsB (x a c : List Bool) : Bool :=
  c.headD false && rootRecB x (nextEnt c) &&
    entAll c fun pre R rest =>
      (decide (pre = []) || occB a R || (isLast rest && flagOf c && occB (tD a) R)) &&
        (!hasNext rest || linkB a R (nextEnt rest)) &&
        (!isLast rest || lastB a c pre R)

/-- **Every task of every expanded method is the next step of some entry.** -/
def childB (a w c : List Bool) : Bool :=
  entAll c fun pre R _ => decide (pre = []) ||
    entAll a fun _ M _ => !decide (kat 0 M = kat 0 R) ||
      occB w (true :: dbl (pre ++ (true :: (kat 0 M ++ kat 1 M))))

/-- **Every task of the initial task network starts some entry.** -/
def rootsB (x w : List Bool) : Bool :=
  x.tails.all fun s => !idPos x s || occB w (true :: dbl (true :: (key 0 ++ dbl (nvAt s))))

/-- **The task `j` is ordered before the task `j'` in the network `k`** (all three doubled
numerals). -/
def ordB (x a k j j' : List Bool) : Bool :=
  (decide (k = key 0) && (preOrdB j j' x && !preOrdB j' j x)) ||
    (!decide (k = key 0) && occB (tO a) (true :: (k ++ (j ++ (j' ++ [false])))))

/-- **Two contents, `cu` listed before `cv`.** -/
def pairB (x a cu cv : List Bool) : Bool :=
  entAny cu fun pre R _ =>
    decide (pre <+: cv) && hasNext (cv.drop pre.length) &&
      decide (kat 0 R = kat 0 (nextEnt (cv.drop pre.length))) &&
      !decide (kat 1 R = kat 1 (nextEnt (cv.drop pre.length))) &&
      (flagOf cu || flagOf cv ||
        !ordB x a (kat 0 R) (kat 1 (nextEnt (cv.drop pre.length))) (kat 1 R))

/-- **Any two entries of the certificate.** -/
def pairsB (x a w : List Bool) : Bool :=
  entAll w fun _ E rest => entAll rest fun _ E' _ => pairB x a (cont E) (cont E')

/-- **The three lists `P` are those of the action whose doubled numeral is `K`.** -/
def actB (a K P : List Bool) : Bool :=
  occB (tA a) (true :: (K ++ (dbl P ++ [false]))) ||
    (!entAny (tA a) (fun _ E _ => decide (kat 0 E = K)) && decide (P = [false, false, false]))

/-- **The three lists of the content `c` are those of its action** (empty for an empty leaf). -/
def rowB (a c : List Bool) : Bool :=
  (flagOf c && decide (p3Of c = [false, false, false])) ||
    (!flagOf c && entAll c fun _ R rest => !isLast rest || actB a (kat 3 R) (p3Of c))

/-- **The entry with content `c` leads from the state `S` to its own state.** -/
def transB (a S c : List Bool) : Bool :=
  subEntB (prOf c) S && subEntB (adOf c) (stOf c) && keepB S (deOf c) (stOf c) &&
    postB (stOf c) (adOf c) S (deOf c) && rowB a c

/-- **The states of the entries form a run from the initial state to a goal state.** -/
def execB (x a w : List Bool) : Bool :=
  (!hasNext w || transB a x (cont (nextEnt w))) && (hasNext w || subEntB (yB x) x) &&
    entAll w fun _ E rest =>
      (!hasNext rest || transB a (stOf (cont E)) (cont (nextEnt rest))) &&
        (!isLast rest || subEntB (yB x) (stOf (cont E)))

/-- **The verifier.** -/
def acV (args : Args) : Bool :=
  blistB (args.getD 2 []) &&
    entAll (args.getD 2 []) (fun _ E _ => parseB (cont E) &&
      recsB (args.getD 0 []) (args.getD 1 []) (cont E) &&
      childB (args.getD 1 []) (args.getD 2 []) (cont E)) &&
    rootsB (args.getD 0 []) (args.getD 2 []) &&
    pairsB (args.getD 0 []) (args.getD 1 []) (args.getD 2 []) &&
    execB (args.getD 0 []) (args.getD 1 []) (args.getD 2 [])

end AcVer

end Syn

end HTN
