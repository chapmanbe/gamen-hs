#!/usr/bin/env python3
"""Build a notebook from a Markdown source file.

The script is idempotent: it strips any previously-spliced ``output``
blocks first, then runs the evals fresh, and writes the result back
to the source path. That keeps Jekyll's source tree as the single
view of truth and makes ``jekyll serve`` work without extra config.

Pipeline:

1. Strip every existing ```output``` block from the source.
2. Find every fenced ```haskell``` code block in the (cleaned) input.
3. Accumulate plain blocks as "context" (definitions, imports).
4. For each block tagged ``{.eval}``, build a runnable Haskell
   program from the accumulated context plus a ``main = print (...)``
   wrapper around the eval block's contents. Run it via
   ``cabal exec -- runghc`` from the repository root so that the
   ``gamen`` library is in scope.
5. Splice the captured stdout back into the document as a sibling
   ``output`` code block.

Usage:
    python3 notebooks/build.py notebooks/01-kripke.md          # rewrites in place
    python3 notebooks/build.py notebooks/01-kripke.md out.md   # write to out.md instead

Conventions:
    ```haskell                  -- shown for reading; added to context.
    foo = ...
    ```

    ```haskell {.eval}          -- treated as a single expression;
    expr                          its print-value goes into ```output```.
    ```

    ```haskell {.ghci}          -- GHCi directive; shown but not extracted.
    :set +m
    ```

    ```bash                     -- left untouched (shown to the reader).
    cabal repl gamen
    ```

A sidecar ``.hs`` file is written to ``notebooks/build/`` (gitignored)
so readers who'd rather ``:l`` the chapter than copy-paste it can use
that file directly.
"""
from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Match plain fenced ```haskell blocks (no Pandoc-style attributes —
# kramdown doesn't understand them and the syntax confuses GitHub's
# raw-markdown viewer; see the README convention table).
HASKELL_BLOCK_RE = re.compile(
    r"^```haskell\s*\n(?P<code>.*?)\n```\s*$",
    re.MULTILINE | re.DOTALL,
)

# Match previously-spliced ```output blocks (and the blank line(s)
# immediately preceding them, so a re-build doesn't pile up blank
# lines on every iteration).
OUTPUT_BLOCK_RE = re.compile(
    r"\n*^```output\n.*?\n```\s*$",
    re.MULTILINE | re.DOTALL,
)


def strip_outputs(text: str) -> str:
    """Remove every ```output``` block left behind by an earlier build."""
    return OUTPUT_BLOCK_RE.sub("", text)


# Marker comments authors use to tag a haskell block. They go on the
# first line of the block as a Haskell-line-comment so they survive
# any Markdown renderer (kramdown, GFM, Pandoc) untouched.
EVAL_MARKER_RE = re.compile(r"^\s*--\s*:eval\b")
GHCI_MARKER_RE = re.compile(r"^\s*--\s*:ghci\b")


def first_line(code: str) -> str:
    return code.splitlines()[0] if code else ""


def is_eval(code: str) -> bool:
    return bool(EVAL_MARKER_RE.match(first_line(code)))


def is_ghci(code: str) -> bool:
    """A ``-- :ghci`` block contains GHCi directives (``:set``, ``:l``,
    ``:t``). Shown to the reader as Haskell-flavoured syntax but
    *not* valid Haskell source, so the build script neither
    accumulates nor evaluates it."""
    return bool(GHCI_MARKER_RE.match(first_line(code)))


def strip_marker(code: str) -> str:
    """Drop the leading ``-- :eval`` / ``-- :ghci`` marker line so the
    body can be wrapped in ``main = print (...)`` cleanly."""
    lines = code.splitlines()
    return "\n".join(lines[1:])


def _scrub_cabal_chatter(stderr: str) -> str:
    """Drop the boilerplate cabal warnings that appear at the top of
    every ``cabal exec`` invocation when the local package list is
    stale. Keeps actual error messages."""
    lines = [
        ln for ln in stderr.splitlines()
        if not ln.startswith("Warning: The package list")
        and not ln.startswith("Run 'cabal update'")
    ]
    return "\n".join(lines).strip()


def run_haskell(program: str, repo_root: Path) -> str:
    """Run a Haskell program via ``cabal exec -- runghc`` and return
    its stdout. On non-zero exit, return the trailing stderr formatted
    as a comment so the failure is visible in the notebook."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".hs", dir=repo_root, delete=False
    ) as f:
        f.write(program)
        tmp = Path(f.name)
    try:
        result = subprocess.run(
            # ``--ghc-arg=-package --ghc-arg=gamen`` exposes the
            # project library to ``runghc``. Plain ``-package gamen``
            # gets eaten by ``runghc`` itself rather than passed
            # through to GHC.
            [
                "cabal", "exec", "--",
                "runghc",
                "--ghc-arg=-package", "--ghc-arg=gamen",
                tmp.name,
            ],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if result.returncode == 0:
            return result.stdout.rstrip()
        # Surface the last few lines of stderr so type errors are
        # legible without scrolling through the cabal preamble.
        scrubbed = _scrub_cabal_chatter(result.stderr)
        tail = "\n".join(scrubbed.splitlines()[-12:])
        return f"-- error (exit {result.returncode}):\n{tail}"
    finally:
        tmp.unlink(missing_ok=True)


def process(text: str, repo_root: Path) -> tuple[str, str]:
    """Walk the document, splicing outputs after each ``-- :eval`` block.

    Returns the processed Markdown plus the concatenated source code
    suitable for ``:load`` in GHCi.
    """
    pieces: list[str] = []
    accumulated: list[str] = []
    cursor = 0

    for m in HASKELL_BLOCK_RE.finditer(text):
        # Pass the markdown up to and including the block through
        # unchanged.
        pieces.append(text[cursor : m.end()])
        cursor = m.end()

        code = m.group("code")

        if is_eval(code):
            body = strip_marker(code)
            program = "\n".join(accumulated)
            # Indent the eval block's body so Haskell's layout rule
            # treats it as the argument to ``print`` rather than a
            # new top-level binding.
            indented = "\n".join("  " + ln for ln in body.splitlines())
            program += f"\n\nmain = print (\n{indented}\n  )\n"
            output = run_haskell(program, repo_root)
            pieces.append(f"\n\n```output\n{output}\n```")
        elif is_ghci(code):
            # GHCi-only directive — visible to the reader, but neither
            # part of the program context nor evaluated.
            pass
        else:
            accumulated.append(code)

    pieces.append(text[cursor:])
    processed_md = "".join(pieces)
    sidecar_hs = "\n\n".join(accumulated) + "\n"
    return processed_md, sidecar_hs


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print(__doc__, file=sys.stderr)
        return 2

    src = Path(sys.argv[1]).resolve()
    out = Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else src

    # Walk upward until we find a .cabal file — that's the repo root
    # cabal exec needs to be invoked from.
    repo_root = src.parent
    while repo_root != repo_root.parent:
        if any(p.suffix == ".cabal" for p in repo_root.iterdir()):
            break
        repo_root = repo_root.parent
    else:
        print("error: could not find a .cabal file above the source", file=sys.stderr)
        return 1

    text = strip_outputs(src.read_text())
    processed_md, sidecar_hs = process(text, repo_root)

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(processed_md)

    # Sidecar Haskell source — gitignored under notebooks/build/.
    sidecar_dir = src.parent / "build"
    sidecar_dir.mkdir(parents=True, exist_ok=True)
    sidecar = sidecar_dir / (src.stem + ".hs")
    sidecar.write_text(sidecar_hs)

    print(f"wrote {out}")
    print(f"wrote {sidecar}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
