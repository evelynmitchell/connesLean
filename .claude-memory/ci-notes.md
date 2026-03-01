# CI & Repo Structure Notes

## GitHub Actions
- Workflows ONLY read from `.github/workflows/` at the **repo root**
- Repo-root CI added in PR #12: `.github/workflows/ci.yml`

## Sorry regression check (PR #20)
- CI step before build: `grep -rnw 'sorry' . --include='*.lean' --exclude-dir='.lake'`
- Uses `-w` for portable word-boundary matching (not `\b` which is PCRE)
- Scans from ConnesLean/ working directory, excludes `.lake/` dependencies
- In docs, reference "sorries" (plural) to avoid grep false positives

## ℝ≥0 notation lint
- CI step: `grep -rn 'ℝ≥0' . --include='*.lean' --exclude-dir='.lake'`
- Catches both `ℝ≥0` and `ℝ≥0∞` (substring match)
- Use `NNReal` / `ENNReal` names instead — the notation parses as 3+ tokens (ℝ, ≥, 0)

## Axiom soundness lint (PR #92)
- CI step: `bash ../scripts/lint_axiom_soundness.sh` (runs from `ConnesLean/` directory)
- 3 checks: `**Soundness:**` annotation, `/--` docstring, inventory sync with `soundness/Main.lean`
- Scans `^\s*axiom ` with `--exclude-dir='.lake' --exclude-dir='soundness'`
- 7 executable cross-checks in `ConnesLeanTest/SoundnessTests.lean`

## Lake build commands
- All lake commands must run from `ConnesLean/` directory
- `lake build ConnesLean` — build the library
- `lake build connes_lspec` — build LSpec test executable
- `lake exe connes_lspec` — run tests
