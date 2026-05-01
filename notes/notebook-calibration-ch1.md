# Calibration: Pluto ch1 vs. gamen-hs `notebooks/01-kripke.md`

Source: `~/Code/Julia/Gamen.jl/notebooks/theory/pluto/ch1_syntax_and_semantics.jl` (563 lines).
Target: `notebooks/01-kripke.md` (175 lines after build splicing).

The Pluto chapter is roughly 3× the length and covers materially more
ground. This note inventories what's there, what my draft has,
what's missing on the Haskell side, and what to do about each.

## Section-by-section diff

| Pluto ch1 section | In my draft? | Plan |
|---|---|---|
| Title + 5 explicit learning outcomes | ✗ no learning outcomes block | **Add** |
| "Why Modal Logic?" motivational intro (LLM critique, brief history of Lewis & Kripke, list of application areas) | ✗ | **Add** — translates directly |
| Language of Basic Modal Logic (Definition 1.1, the 5-element list) | partial (no formal numbered list) | **Add** the numbered list |
| Atomic Formulas — by name, by index | partial | **Adapt** — gamen-hs `Atom` is by-name only; either drop the index variant or convention `Atom "p_0"` |
| Building Formulas (Definition 1.2) — Bottom, Top, Not, And, Or, Implies, Iff | partial (only Box, Diamond shown) | **Add** all connectives |
| Unicode Syntax (`□` / `◇` aliases) | ✗ | **Adapt** — gamen-hs has no Unicode aliases; either add them as a `Gamen.Formula.Unicode` module or note the absence |
| Practice: Translate English to Formulas (7 exercises with hidden hints) | ✗ | **Add** — uses `<details>` HTML instead of Pluto Admonitions |
| Modal-Free Formulas | ✓ partial | **Expand** with the KR Lens sidenote |
| KR Lens: Formal Syntax as Medium (Davis et al. 1993) | ✗ | **Add** — recurring sidenote pattern across the Julia track |
| Practice: Modal or Not? (6 exercises) | ✗ | **Add** |
| Relational Models (Definition 1.6) — three components, "what are worlds?" | ✗ | **Add** — definitional |
| Tic-tac-toe + clinical examples (Admonition asides) | ✗ | **Add** as marginnotes |
| Figure 1.1 prose description | ✓ partial | **Expand** with explicit V(p), V(q) listing |
| Frame + Model construction | ✓ | (already present) |
| `visualize_model` graph rendering | ✗ | **Adapt** — gamen-hs has no visualize. Either (a) generate a static `.svg` via `dot` from a Kripke→GraphViz helper, (b) embed a hand-drawn ASCII diagram, (c) skip and rely on the prose. **Lean (a)** for a real teaching artefact |
| KR Lens: Kripke Models as Surrogates | ✗ | **Add** as sidenote |
| Truth at a World (Definition 1.7, full table of 8 clauses) | ✗ | **Add** — the table is a teaching anchor |
| Problem 1.1 from B&D (9 items walked through, with interpretive prose) | partial (~3 items) | **Expand to all 9** |
| Practice: Evaluate Formulas (5 exercises) | partial (one exercise) | **Add the other four** |
| Duality of □ and ◇ (Proposition 1.8) — verification at every world | ✗ | **Add** |
| Truth in a Model (Definition 1.9) — `is_true_in` | ✗ | **Add** — `Gamen.Semantics.isTrueIn` already exists |
| Entailment (Definition 1.23) — 2-world example | ✗ | **Add** — `Gamen.Semantics.entails` already exists |
| Practice: Translate and Check (3 exercises) | ✗ | **Add** |
| Exploring on Your Own + template | partial (one exercise) | **Expand** to match |

## Haskell-specific additions (not in the Pluto)

These should be explicit in the gamen-hs version because they're
the differentiators of doing this in Haskell rather than Julia:

1. **Exhaustive pattern matching as a teaching point.** The
   `Formula` ADT is closed; any function over it (`satisfies`,
   `isModalFree`, `atoms`) must handle all 25 constructors, and GHC
   warns at compile time if you miss one. The Pluto notebook can't
   say this — Julia uses multiple dispatch. Drop a one-paragraph
   sidenote at the "Building Formulas" section.
2. **Type signature for `satisfies`.** `satisfies :: Model -> World
   -> Formula -> Bool` makes the function's role visible at a
   glance. Worth a small inline note when introducing the call.
3. **`Atom` newtype + pattern synonym.** The Pluto chapter uses
   `Atom(:p)` (Symbol-keyed); gamen-hs uses `Atom "p"` (String-
   keyed via a bidirectional pattern synonym). Note this once and
   move on; don't dwell.
4. **GHCi workflow.** Already present in my draft (`:set +m`,
   `cabal repl gamen`). Keep.

## Things to drop or simplify

- **Unicode `□` / `◇` aliases.** Gamen-hs doesn't have them. Adding
  a `Gamen.Formula.Unicode` module is ~10 lines but introduces a
  conceptual fork ("which constructor is canonical?"). Recommend
  *not adding* and instead noting that the pretty-printer renders
  `Box (Atom "p")` as `□p` already.
- **Atom by index** (`Atom(0)`, `Atom(1)`). Gamen-hs `Atom` is
  String-keyed. Either drop the by-index demo or use the
  String convention `Atom "p_0"`. Recommend drop.

## Visualization decision

The biggest open call. Three options:

| Option | Cost | Fidelity to Pluto |
|---|---|---|
| (a) Add a `Gamen.Visualize.toGraphviz :: Frame -> Text` helper, then `dot -Tsvg` in `build.py` | ~30 min for the helper + ~20 min Makefile glue | High — actual rendered graph |
| (b) Embed hand-drawn SVG / `<pre>` diagrams in the Markdown | 10 min per chapter | Medium — static |
| (c) Skip the visualization | 0 | Low — text-only |

**Recommendation: (a)**. Once written, every subsequent chapter
reuses the helper for its own model. The cost is one-time. Option
(b) doesn't scale beyond the first chapter; (c) leaves a noticeable
gap relative to the Pluto track.

## Pluto-specific patterns and their Markdown analogs

| Pluto idiom | Markdown / Jekyll equivalent |
|---|---|
| `Markdown.Admonition("hint", "Reveal answer", […])` | `<details><summary>Reveal answer</summary>…</details>` (works in GitHub + kramdown) |
| `Markdown.Admonition("note", "...")` for KR Lens / Examples | `{% include sidenote.html … %}` we already have |
| Plot/figure cells | the proposed `Gamen.Visualize` + `dot` pipeline |
| `@bind` interactive widgets | drop (Pluto-only); replace with "edit this and re-run" prose |
| Reactive cell ordering | linearise; the chapter is already a single thread |

## Estimated effort

- Hint-revealing exercises × 21 (7 + 6 + 5 + 3): mechanical.
  Maybe 2 hours total.
- Definition table copies (1.1, 1.2, 1.6, 1.7, 1.9, 1.23): 1 hour.
- Motivational intro / why-modal-logic / KR Lens sidenotes: 1.5 hours.
- Visualization helper + Makefile integration: 1 hour.
- Tic-tac-toe / clinical examples as marginnotes: 30 minutes.
- B&D Problem 1.1 walkthrough (9 items): 1 hour.
- Duality / truth-in-model / entailment sections: 1 hour.

**Total: ~8 hours of focused work for a fully calibrated ch1.**
The first chapter sets the template; subsequent chapters should be
faster (probably 4–6 hours each since the framing pieces — KR Lens
voice, hint patterns, sidenote conventions — get reused).

## Recommendation

**Do the calibration now**, before drafting any further chapters.
Reasons:

1. The structural decisions (visualization helper, Admonition →
   `<details>` mapping, KR Lens sidenote conventions) all need to
   be made once and reused. Discovering them later would force
   retrofits.
2. Chapter 1 is the on-ramp. If a reader doesn't get hooked here,
   they don't reach the gamen-hs-specific material in chapters 6
   (tableau) and the deontic-STIT-prover chapter that has no
   Julia counterpart.
3. The Pluto track was written carefully — the seven translation
   exercises in particular are good pedagogy. Reproducing them is
   higher leverage than inventing new material.

Suggested execution order:

1. Add `Gamen.Visualize` (the GraphViz helper).
2. Update `notebooks/01-kripke.md` against the Pluto ch1 outline,
   in one or two passes.
3. Run `make build && make serve` and eyeball.
4. Iterate on the Tufte CSS for `<details>` blocks if they look
   wrong.
5. Commit.

After ch1 lands cleanly, ch6 (tableau) is the next high-value
chapter — the gamen-hs prover is more substantial than Gamen.jl's,
so this becomes the chapter where Haskell shines.
