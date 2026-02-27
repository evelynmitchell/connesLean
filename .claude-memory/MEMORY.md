# ConnesLean Project Memory

## Project State
- **Stage 1**: Complete. All 9 sorries closed, PRs #9-#18 merged.
- **Stage 2**: Complete. 8 PRs merged, 0 sorries (PRs #28-#36, Issues #19-#27).
- CI sorry regression check added (grep -rnw in CI, blocks merge)
- **Stage 4**: Complete. 5 PRs merged (PRs #45-#49, Issues #40-#44).
- **Stage 5**: Complete. 5 PRs merged, 0 sorries, 9 axioms (PRs #55-#60, Issues #50-#54).
- **Stage 6**: Redo planned. Previous PRs (#66-#70) superseded.
  - Issues: #61 (6A), #62 (6B), #63 (6C), #64 (6D), #65 (6E)
  - Redo all 5 files from scratch with proper discipline:
    1. Plan each file → get user review → then implement
    2. Write in 100-150 line chunks, diagnostics after each
    3. Don't move to next file until current is clean and user has seen it
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
