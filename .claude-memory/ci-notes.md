# CI & Repo Structure Notes

## GitHub Actions workflow location
- GitHub Actions ONLY reads `.github/workflows/` from the **repo root**
- Workflows under `ConnesLean/.github/workflows/` are silently ignored
- Repo-root CI added in PR #12: `.github/workflows/ci.yml`
- The old workflows (lean_action_ci.yml, update.yml, create-release.yml) under ConnesLean/ never ran

## Sorry regression check (PR #20)
- Added as CI step before build: `grep -rnw 'sorry' . --include='*.lean' --exclude-dir='.lake'`
- Uses `-w` for portable word-boundary matching (not `\b` which is PCRE)
- Scans from ConnesLean/ working directory, excludes `.lake/` dependencies
- Sorries live on feature branches; CI blocks merge to main
- In docs, reference "sorries" (plural) to avoid grep false positives

## Lake build commands
- All lake commands must run from `ConnesLean/` directory (or use `working-directory:` in CI)
- `lake build ConnesLean` — build the library
- `lake build connes_lspec` — build LSpec test executable
- `lake exe connes_lspec` — run tests
