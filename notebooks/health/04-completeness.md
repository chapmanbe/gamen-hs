---
title: "Completeness — Silence Means Safety"
layout: notebook
chapter: "Health 4"
---

# Completeness — Silence Means Safety

*Theory ch4* established the completeness theorem: every valid
formula is derivable, and equivalently, every consistent set has
a model. This chapter explains why that matters for clinical
decision support.

## Setup

```haskell
import Gamen.Formula
import Gamen.Tableau

aspirin      = Atom "aspirin"
afib         = Atom "afib"
bleeding     = Atom "active_bleeding"
anticoag     = Atom "anticoagulant"
```

## The Operational Promise

A CDS checker reports one of two verdicts on a set of guidelines:

- **Conflict found.** The guidelines are inconsistent — they
  *cannot* all be jointly satisfied. The clinician needs to
  resolve this before deploying the rule set.
- **No conflict found.** The guidelines are consistent — there
  *exists* a model where they all hold simultaneously.

The completeness theorem is what makes the second verdict
trustworthy. Without completeness, "no conflict found" might mean
"my prover wasn't strong enough to find the conflict." With
completeness, it really means "no conflict exists."

For `gamen-hs`, the operational test is `tableauConsistent`. If
it returns `True`, the underlying model exists.

## A Realistic Three-Guideline Scenario

Three real(ish) cardiovascular guidelines:

```haskell
g1 = Implies afib (Box anticoag)                          -- "AFib ⇒ obligatory anticoag"
g2 = Implies bleeding (Box (Not anticoag))                -- "Bleeding ⇒ obligatory NO anticoag"
g3 = Implies (And afib bleeding) (Box (Not anticoag))     -- "AFib + bleeding ⇒ hold anticoag"
```

Are they jointly consistent in KD?

```haskell
-- :eval
tableauConsistent systemKD [g1, g2, g3]
```


```output
True
```
`True`. The three rules don't contradict each other — `g3` is
the *resolution* of the apparent conflict between `g1` and `g2`.
Note that `g1` alone is fine, `g2` alone is fine, and `g3`
covers the joint case. In a model with neither AFib nor bleeding,
all three are vacuously satisfied.

Now drop `g3` (forget about the resolution rule):

```haskell
-- :eval
tableauConsistent systemKD
  [ g1
  , g2
  , afib
  , bleeding
  ]
```


```output
False
```
`False`. Without `g3`, the guidelines force both
$\square$anticoag (from `g1` + AFib) and $\square \neg$anticoag
(from `g2` + bleeding) — KD-inconsistent. This is exactly the
kind of case CDS conflict-detection is supposed to flag.

## Why Without Completeness This Wouldn't Work

Imagine a CDS prover that's *sound but incomplete* — it never
falsely reports a conflict, but it might miss real ones. A
clinician deploying that system who sees "no conflict found"
can't trust the verdict. They have to assume the system might be
silent on real conflicts and re-verify by hand — completely
defeating the purpose.

The completeness theorem says every consistent set has a model;
its contrapositive says every inconsistent set is detectable.
Thanks to soundness AND completeness, gamen-hs's
`tableauConsistent` is *both* directions: a `True` answer is a
guarantee, and a `False` answer is also a guarantee.

Combine with the **finite model property** (theory ch5) and
you get the full operational promise: every consistency check
terminates, and the answer is the truth.

## Compactness for Large Guideline Sets

Compactness — a corollary of completeness — says: a set of
formulas is consistent iff *every finite subset* is consistent.

For a CDS deployment with 1,000 rules, this lets you slice and
test:

- If consistency-check on a 50-rule subset fails, the full set
  fails. (Sound direction.)
- If every $k$-rule subset for some $k$ is consistent, the full
  set is consistent. (Compactness direction.)

In practice this means progressive deployment is safe: if you've
verified each guideline-bundle individually and they remain
consistent in pairs, you have strong (though not air-tight)
evidence that the joint deployment is consistent.

### Exercise

**1.** A consultant says "I added a new rule and the CDS prover
silently rejected it without flagging an error." Without
completeness, what could be going wrong?

<details><summary>Reveal answer</summary>
Without completeness, the prover could be too weak to detect
that the new rule contradicts existing rules. The verdict
"silently accepted" would be unreliable. With completeness,
the prover always reaches a verdict — either consistent (with
a model existing) or inconsistent (with a derivable
contradiction).
</details>

**2.** Why does compactness suggest a strategy of "test in
chunks" for a large guideline set?

<details><summary>Reveal answer</summary>
Compactness says the whole set is consistent iff every finite
subset is. So if you partition your 1,000 rules into 50-rule
bundles and verify each bundle individually, you've covered
the consistency of every subset of size ≤ 50. You haven't
proven joint consistency unless you check all subsets, but
you've ruled out all "small" inconsistencies — and small
inconsistencies are by far the most common kind in real
guidelines.
</details>

---

*Next chapter: decidability — guarantee that the prover always
terminates.*
