# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains Christopher Long's proof of the Restricted Weil Quadratic Form, intended for formalization in Lean. Currently the mathematical content exists as a LaTeX document (`lamportform.tex`) using Lamport-style structured proofs. No Lean code has been written yet.

## Repository Structure

- `lamportform.tex` — Main mathematical document: "Energy Decomposition, Compact Resolvent, and Perron-Frobenius Properties of the Restricted Weil Quadratic Form"
- `bootstrap.sh` — Development environment setup script (installs uv, ruff, shellcheck, pre-commit, Claude Code)

## Common Commands

### Environment Setup
```bash
./bootstrap.sh          # Install all dev tools for detected environment
./bootstrap.sh --check  # Check what's installed without making changes
```

### Building the LaTeX Document
```bash
pdflatex lamportform.tex
```

### Linting
```bash
shellcheck bootstrap.sh   # Lint shell scripts
ruff check .              # Lint Python files (when added)
```

## LaTeX Document Structure

The document uses Lamport's hierarchical structured-proof format where each step states a claim with justifications, and sub-steps provide expandable detail. Key mathematical topics covered:

1. Multiplicative structures and dilation operators on R_+*
2. Local explicit-formula terms (prime and archimedean)
3. Energy decomposition into translation differences
4. Markov property and translation-invariance
5. Irreducibility, compact resolvent, and operator realization
6. Positivity-improving semigroups and ground state existence
7. Evenness of ground state from inversion symmetry

## Bootstrap Script Environment Detection

The bootstrap script auto-detects 8 environments: `claude-cli`, `claude-code`, `codespaces`, `github-actions`, `devcontainer`, `container`, `vscode`, `local`. Pre-commit hooks are intentionally skipped in the `claude-code` environment.
