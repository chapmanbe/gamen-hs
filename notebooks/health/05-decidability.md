---
title: "Decidability — Termination Guarantees for Clinical Provers"
layout: notebook
chapter: "Health 5"
---

# Decidability — Termination Guarantees for Clinical Provers

*Theory ch5* introduced filtrations and the finite model property
that imply decidability of K, KT, KD, S4, S5. This chapter
applies that guarantee to clinical settings: a CDS prover that
*always terminates*.

## Setup

```haskell
import Gamen.Formula
import Gamen.Tableau

statin     = Atom "statin"
diabetes   = Atom "diabetes"
chf        = Atom "chf"
arrhythmia = Atom "arrhythmia"
```

## What Decidability Buys

A consistency check with a 30-second timeout that times out
gives you no information. A consistency check that *always
returns* — yes or no, in finite time — gives you a verdict you
can act on.

For modal logics K through S5, including KDt and the deontic
STIT logic in `Gamen.DeonticStit.Prove`, every check is
guaranteed to return. The blocking mechanism inside the tableau
prover (see `notes/tableau_blocking.md`) is what enforces this.

## Stress-Testing with Many Atoms

A clinical-guideline checker might receive a few hundred atoms
in real deployments (one per atomic clinical state). Tableau
proof search is exponential in the worst case (multi-agent
modal logic is NEXPTIME-complete; Balbiani et al. 2008), but
clinical inputs are far from worst case — formulas have few
nesting levels, few interacting modal operators per atom.

Try a 10-atom CDS scenario:

```haskell
manyRules =
  [ Implies (Atom "diabetes") (Box (Atom "statin"))
  , Implies (Atom "chf") (Box (Atom "ace_inhibitor"))
  , Implies (Atom "afib") (Box (Atom "anticoag"))
  , Implies (Atom "asthma") (Box (Atom "inhaler"))
  , Implies (Atom "htn") (Box (Atom "antihypertensive"))
  , Implies (Atom "depression") (Box (Atom "ssri"))
  , Implies (Atom "renal_fail") (Box (Atom "dialysis"))
  , Implies (Atom "copd") (Box (Atom "bronchodilator"))
  , Implies (Atom "pneumonia") (Box (Atom "abx"))
  , Implies (Atom "stroke") (Box (Atom "tpa"))
  ]
```

```haskell
-- :eval
tableauConsistent systemKD manyRules
```

```output
True
```
Returns near-instantly. Decidability is operational.

## Adding a Conflict

Inject a single conflict into the bundle — a patient who has CHF
and is in hypotensive shock at the same time, where one rule
says "no fluids" and the other says "fluids":

```haskell
conflictPair =
  [ Box (Not (Atom "fluids"))   -- CHF: hold fluids
  , Box (Atom "fluids")         -- shock: give fluids
  ]
```

```haskell
-- :eval
tableauConsistent systemKD conflictPair
```

```output
False
```
`False` — the conflict is detected. Crucially, the prover *also
terminates* on the inconsistent input. Decidability means both
"yes" and "no" verdicts are reachable.

A practical note: tableau search is *exponential in the worst
case* (one new branch per disjunctive rule). When you bundle a
real conflict in with many unrelated implications, the
implication-driven branching may exhaust the search budget
before the modal contradiction is reached. The
`gamen-validate check_consistency` dispatcher mitigates this by
running consistency checks on each formula's *direct
projections* alongside the joint check, so a small modal
conflict surfaces even inside a noisy rule bundle.

## When the Prover Says No: What Comes Next

When `tableauConsistent` returns `False`, the underlying
tableau is closed — every branch reached a contradiction. The
*open branches* (none, in this case) would be the counter-
examples. For an open prover (`tableauConsistent` returns
`True`), the open branch is exactly the witness model.

This is the mechanism behind `Gamen.Tableau.extractCountermodel`:
when you want a *concrete clinical scenario* that satisfies all
the rules — not just a yes/no on consistency — you can extract
one. Useful for sanity-checking that your guideline encoding
admits the scenarios you intended.

```haskell
-- A non-trivial yes verdict, with a witness model available
tab = buildTableau systemKD
  [ pfTrue (mkPrefix [1]) (Atom "diabetes")
  , pfTrue (mkPrefix [1]) (Box (Atom "statin"))
  ] 1000
```

```haskell
-- :eval
( length (tableauBranches tab)
, all isClosed (tableauBranches tab)
)
```

```output
(1,False)
```
One open branch — the consistency witness.

### Exercise

**1.** Why does "decidable" not mean "fast"? What's the practical
difference between decidability and tractability?

<details><summary>Reveal answer</summary>
Decidability means there exists a procedure that always
terminates with the correct answer. Tractability means it does
so in <em>polynomial</em> time. Modal logic is decidable but
multi-agent modal logic is NEXPTIME-complete (Balbiani et al.
2008) — exponential in the worst case. For clinical-scale inputs
(tens to hundreds of atoms, low modal nesting), the worst case
rarely materialises.
</details>

**2.** What happens in `gamen-hs` when a tableau search hits
the <code>maxSteps</code> bound?

<details><summary>Reveal answer</summary>
<code>buildTableau</code> returns the partial tableau with
whatever branches are unfinished. The blocking machinery
prevents this from happening on any input we've encountered in
practice. The bound is a safety net for catastrophic blow-up —
you'd see it only if a future input triggered a bug, not in
normal operation.
</details>

---

*Next chapter: conflict detection — using gamen-validate at the
JSON-Lines boundary.*
