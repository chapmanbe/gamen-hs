---
title: "Notebooks"
layout: notebook
---

# gamen-hs notebooks

Pedagogical chapters that introduce the library by working through
small examples in GHCi. Read each chapter alongside an open
`cabal repl gamen` session and copy the code blocks as you go; every
`{.eval}`-marked block has its expected output captured in the
chapter so you can compare what your shell produces.

## Chapters

1. [Kripke Frames and Satisfaction](01-kripke.html) — the basics
   from B&D Chapter 1; build Figure 1.1 and verify a few modal
   formulas.
{: .ordered }

The companion API documentation lives at the
[Haddock pages](../) for this project.

---

*The chapter sources are plain Markdown (`notebooks/*.md`) with
fenced Haskell blocks. The `notebooks/build.py` script runs each
`{.eval}` block through `cabal exec -- runghc` and splices the
output back into the document before Jekyll renders it.*
