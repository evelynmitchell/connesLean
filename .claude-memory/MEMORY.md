# ConnesLean Project Memory

## Project State
- **Stage 1**: Complete. All 9 sorries closed, PRs #9-#18 merged.
- **Stage 2**: Complete. 8 PRs merged, 0 sorries (PRs #28-#36, Issues #19-#27).
- CI sorry regression check added (grep -rnw in CI, blocks merge)
- **Stage 4**: Complete. 5 PRs merged (PRs #45-#49, Issues #40-#44).
- **Stage 5**: Complete. 5 PRs merged, 0 sorries, 9 axioms (PRs #55-#60, Issues #50-#54).
- **Stage 6**: Re-split into 8 files. Previous code reverted, old issues closed.
  - **#71 (6A-i IndicatorEnergy)**: Done. PR #78, 253L, 0 extra axioms.
  - #72 (6A-ii EnergyPositivity ~150L)
  - #62 (6B InvarianceSplit ~130L, unchanged)
  - #73 (6C ConstantInDomain ~250L)
  - #74 (6D-i NormInequality ~200L), #75 (6D-ii EnergyEquality ~200L), #76 (6D-iii CrossVanishing ~200L)
  - #77 (6E Irreducibility ~80L)
  - Chain: #71 → #72 → #73 → #74 → #75 → #76 → #77, with #62 → #73
  - Discipline: plan → user review → implement in 100-150 line chunks
- **Axiom elimination roadmap**: `docs/axiom-elimination-roadmap.md`
  - 9 of 10 axioms eliminable (~760 lines), kato_operator stays as axiom

## Workflow
- **One PR per session**, push for Copilot review, wait for user approval, then merge
- Each PR branch from main, target main; don't use `--delete-branch` on merge
- **Include tests in every PR** — don't batch tests into a separate final PR
- Use plan → **get user review of plan** → MCP API verification → implement
- **Never skip plan review.** Always present the plan and wait for approval before implementing.
- **CRITICAL: Write Lean files in ~100-150 line chunks**, checking `lean_diagnostic_messages` after each. Never write >200 lines without a diagnostics check.

## Style & Naming
- **Prefer Mathlib lemmas over manual proofs**
- Use `cutoffLambda` (not `λ`, `Λ`, or `Lam`) for the cutoff parameter
- Use `refine` (not `apply`) when lemma has mixed term/prop arguments

## Key Learnings
- See [lean-patterns.md](lean-patterns.md) for Lean/Mathlib patterns
- See [ci-notes.md](ci-notes.md) for CI and repo structure notes
- See [review-lessons.md](review-lessons.md) for planning and review process lessons

## Environment
- `lake` requires `export PATH="$HOME/.elan/bin:$PATH"` in Codespaces
- Lean toolchain: v4.28.0, Mathlib v4.28.0
- lean-lsp MCP server configured (`.mcp.json`), verified working
