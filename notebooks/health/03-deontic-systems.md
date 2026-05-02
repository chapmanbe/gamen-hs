---
title: "Deontic Systems for Clinical Decision Support"
layout: notebook
chapter: "Health 3"
---

# Deontic Systems for Clinical Decision Support

*Theory ch3* presented the named modal systems K, KD, KT, K4, S4,
S5 and their axiom schemas. This chapter applies them to clinical
decision support: which system is the right backbone for a CDS
checker, and what does that choice commit you to?

## Setup

```haskell
import Gamen.Formula
import Gamen.Tableau

statin     = Atom "statin"
ascvd      = Atom "ascvd"
ldl_high   = Atom "ldl_high"
allergy    = Atom "statin_allergy"
```

## A Statin Guideline in KD

The simplified ASCVD/cholesterol guideline:

> "If a patient has ASCVD risk and elevated LDL, statin therapy
> is **obligatory** (unless contraindicated)."

```haskell
rule_statin = Implies (And ascvd ldl_high) (Box statin)
exception   = Implies allergy (Diamond (Not statin))
```

The first formula says "if ASCVD and high LDL, then it is
obligatory that the patient is on a statin." The second says
"if there is an allergy, it is permissible *not* to be on a
statin."

Are these two rules jointly consistent in KD?

```haskell
-- :eval
tableauConsistent systemKD [rule_statin, exception]
```

```output
True
```
`True` — they're consistent. Different patient scenarios
(allergy vs. no allergy) trigger different obligations.

What if we add a patient who has BOTH ASCVD+high LDL AND a
statin allergy? Is the resulting set still consistent?

```haskell
-- :eval
tableauConsistent systemKD
  [ rule_statin
  , exception
  , ascvd
  , ldl_high
  , allergy
  ]
```

```output
False
```
`False`. Combined, the rules force $\square$statin (from
ASCVD+highLDL) AND $\diamond \neg$statin (from allergy). In KD
this is impossible: $\square$statin says every deontic
alternative has statin; $\diamond \neg$statin says some
alternative doesn't. The exception clause as written is *too
strong* — it asserts "permitted to skip" without first
suspending the original obligation. A better encoding would
*qualify* the obligation: $\square (\neg \text{allergy} \to
\text{statin})$ — "obligated to be on a statin **unless**
allergic." That formulation IS consistent with the allergy
state. Logic catches the encoding bug.

The simpler contradiction case below shows the same machinery on
a clean conflict:

```haskell
-- :eval
tableauConsistent systemKD
  [ Box statin             -- patient ought to take statin
  , Box (Not statin)       -- patient ought NOT to take statin
  ]
```

```output
False
```
`False` — directly contradictory obligations. This is the case
KD seriality catches: every successor would have to satisfy both
$p$ and $\neg p$, impossible.

## Why Not S5?

A natural question: shouldn't I use S5 (the strongest standard
logic) since it has the most theorems? No — S5 has *too many*
theorems for guideline reasoning. Among them, $\square p \to p$
(reflexivity) and $\diamond p \to \square \diamond p$
(euclideanness). The first says obligations entail actual states
(wrong for obligations); the second says possibility is
necessarily possible (a strong introspection claim).

For pure obligation-checking, **KD** is right. For epistemic
reasoning about a clinician's knowledge, **S5** is right (or at
least KT). For combined deontic + temporal, **KDt** (theory ch14)
is right. Don't use a stronger logic than your domain requires.

```haskell
-- :eval
( tableauProves systemKD [] (Implies (Box statin) statin)  -- T fails in KD
, tableauProves systemS5 [] (Implies (Box statin) statin)  -- T holds in S5
)
```

```output
(False,True)
```
Picking S5 for obligations would *prove* "if statin is
obligatory, the patient is taking it" — useless and false in
practice.

### Exercise

**1.** A guideline checker is built on KD. Can it prove "if
patient should be on statin, then statin is permissible"?

<details><summary>Reveal answer</summary>
Yes — that's Schema D, the defining axiom of KD. <code>tableauProves
systemKD [] (Implies (Box statin) (Diamond statin))</code> returns
<code>True</code>.
</details>

**2.** A clinical guideline mentions "knowledge of the patient's
allergy history." What logic would you use for the *clinician's
knowledge* component, separate from the obligation component?

<details><summary>Reveal answer</summary>
KT or S5 for knowledge. <code>K_clinician (allergy)</code> entails
<code>allergy</code> by Schema T (factivity). In a multi-modal
system, you'd combine: deontic <code>Box</code> on KD-frames for
obligations, epistemic <code>Knowledge</code> on KT/S5-frames
for knowledge. <code>gamen-hs</code>'s <code>Gamen.Epistemic</code>
covers the epistemic side.
</details>

---

*Next chapter: completeness in the clinical context — what
"silence means safety" buys us in CDS.*
