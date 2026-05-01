# gamen-hs notebooks build & serve targets.
#
# Run from the repository root or from within notebooks/.
#
# Targets:
#   make install  — bundle install (one-time gem setup)
#   make build    — run output capture for every chapter
#   make serve    — build + jekyll serve at http://127.0.0.1:4000
#   make clean    — drop the gitignored build artefacts and _site
#
# Ruby toolchain: the system Ruby on macOS (2.6.x) is too old. Use
# Homebrew's: `brew install ruby`, then put its bin and gems on PATH:
#
#   export PATH="$(brew --prefix ruby)/bin:$(brew --prefix)/lib/ruby/gems/4.0.0/bin:$PATH"
#
# (Add to your shell rc or invoke via `make RUBY_PATH=... serve` ad hoc.)

CHAPTERS      := $(wildcard $(dir $(lastword $(MAKEFILE_LIST)))*-*.md)
NOTEBOOKS_DIR := $(dir $(lastword $(MAKEFILE_LIST)))

# Prefer Homebrew Ruby when available; fall back to whatever's on PATH.
BREW_RUBY_BIN  := $(shell brew --prefix ruby 2>/dev/null)/bin
BREW_GEMS_BIN  := $(shell brew --prefix 2>/dev/null)/lib/ruby/gems/4.0.0/bin

# Cabal/GHC live under ghcup; Make starts with a minimal PATH so we
# need to prepend the toolchain explicitly for the build target.
GHCUP_BIN      := $(HOME)/.ghcup/bin

SHELL_PATH     := $(GHCUP_BIN):$(BREW_RUBY_BIN):$(BREW_GEMS_BIN):$(PATH)

.PHONY: build serve clean install

build:
	@for ch in $(CHAPTERS); do \
		echo "→ $$ch" ; \
		PATH=$(SHELL_PATH) python3 $(NOTEBOOKS_DIR)build.py $$ch ; \
	done

install:
	cd $(NOTEBOOKS_DIR) && PATH=$(SHELL_PATH) bundle install

serve: build
	cd $(NOTEBOOKS_DIR) && PATH=$(SHELL_PATH) bundle exec jekyll serve --baseurl ""

clean:
	rm -rf $(NOTEBOOKS_DIR)build $(NOTEBOOKS_DIR)_site
