# CI & Repo Structure Notes

## GitHub Actions
- Workflows ONLY read from `.github/workflows/` at the **repo root**
- Repo-root CI added in PR #12: `.github/workflows/ci.yml`

## Sorry regression check (PR #20)
- CI step before build: `grep -rnw 'sorry' . --include='*.lean' --exclude-dir='.lake'`
- Uses `-w` for portable word-boundary matching (not `\b` which is PCRE)
- Scans from ConnesLean/ working directory, excludes `.lake/` dependencies
- In docs, reference "sorries" (plural) to avoid grep false positives

## Lake build commands
- All lake commands must run from `ConnesLean/` directory
- `lake build ConnesLean` — build the library
- `lake build connes_lspec` — build LSpec test executable
- `lake exe connes_lspec` — run tests
