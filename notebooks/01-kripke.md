---
title: "Kripke Frames and Satisfaction"
layout: notebook
chapter: 1
---

# Kripke Frames and Satisfaction

This chapter introduces Kripke frames and the satisfaction relation
{% include sidenote.html id="bd-1-6" content="Boxes and Diamonds, Definitions 1.6 and 1.7. The local PDF lives at <code>notes/bd-screen.pdf</code>." %} —
the mathematical foundation everything else in `gamen-hs` is built on.
By the end you will have constructed Figure 1.1 of B&D in code and
verified the truth of a few modal formulas at its worlds.

## Setup

Open GHCi against the project's library from the repository root:

```bash
cabal repl gamen
```

Modern GHCi accepts multi-line definitions when they're wrapped in
`:{ ... :}` brackets. If you want to paste several lines without the
brackets every time, turn on multi-line mode:

```haskell {.ghci}
:set +m
```

Now bring the relevant modules into scope:

```haskell
import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics
import qualified Data.Set as Set
```

{% include marginnote.html id="ghci-tip" content="Imports go one per line in GHCi; no brackets needed. If you forget one and a later line errors, just paste the missing import and continue." %}

## A First Frame

The simplest Kripke frame has one world and no accessibility relation
at all:

```haskell
oneWorld = mkFrame ["w"] []
```

We can ask which worlds are reachable from `w`:

```haskell {.eval}
accessible oneWorld "w"
```

The empty set, as expected — no relation means no reachable worlds.

A modal Box claim like `□p` is *vacuously* true at a world with no
successors: there are no counterexamples to find. Build a model with
no atoms valuated and confirm:

```haskell
emptyModel = mkModel oneWorld []
```

```haskell {.eval}
satisfies emptyModel "w" (Box (Atom "p"))
```

## Figure 1.1

B&D's Figure 1.1 has three worlds — `w1`, `w2`, `w3` — with `w1`
reaching both `w2` and `w3`, plus a valuation that puts `p` at `w1`
and `w2`, and `q` at `w2` only:

{% include marginnote.html id="bd-fig-1-1" content="The figure is reproduced in <code>notes/bd-screen.pdf</code> on page 14. Drawing it on paper before reading on helps." %}

```haskell
frame11 = mkFrame ["w1", "w2", "w3"]
                  [("w1", "w2"), ("w1", "w3")]
model11 = mkModel frame11
                  [("p", ["w1", "w2"]), ("q", ["w2"])]
```

Now we can evaluate any formula at any world. Does `□p` hold at `w1`?

```haskell {.eval}
satisfies model11 "w1" (Box (Atom "p"))
```

`p` holds at `w2` but not at `w3`, so `□p` is false at `w1` — the
universal quantifier over successors fails on `w3`. What about `◇q`?

```haskell {.eval}
satisfies model11 "w1" (Diamond (Atom "q"))
```

`q` holds at `w2`, which is one of `w1`'s successors, so `◇q` is
true. The dual operators behave as you'd expect: `□p` says "every
successor satisfies p", `◇p` says "some successor does".

A more subtle question: does `□(p ∨ q)` hold at `w1`? Every
successor of `w1` either has `p` or `q` (or both) — `w2` has both,
`w3` has neither.

```haskell {.eval}
satisfies model11 "w1" (Box (Or (Atom "p") (Atom "q")))
```

False, because `w3` has neither. The conjunction `p ∧ q` doesn't
hold there either. This is the kind of fact tableau provers will
mechanise in [Chapter 2]{.sidenote}.

## Modal-Free Formulas

A formula with no modal operators is decided entirely by the
valuation at the world in question — the accessibility relation
plays no role. The library exposes this as `isModalFree`:

```haskell {.eval}
isModalFree (And (Atom "p") (Not (Atom "q")))
```

Compare with a formula that contains a `Box`:

```haskell {.eval}
isModalFree (Box (Atom "p"))
```

This distinction matters when we get to tableau search: modal-free
formulas can be decided by the propositional rules alone, without
ever creating a fresh world.

## Exercise

Modify `frame11` so that `□p` holds at `w1`. The simplest fix is to
remove the edge to `w3`, but that changes the structure beyond
recognition. A more interesting fix is to add `p` to the valuation
of `w3`. Try both, evaluate `satisfies` to confirm, and think about
which version preserves the *spirit* of the original figure.

---

*Next chapter: prefixed tableau and the closure rule.*
