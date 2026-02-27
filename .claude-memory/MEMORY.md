# ConnesLean Project Memory

## Project State
- **Stage 1**: Complete. All 9 sorries closed, PRs #9-#18 merged.
- **Stage 2**: Complete. All 8 PRs merged, 0 sorries.
  - PR A: rpDivEquiv refactor (#28, merged) — Issue #19
  - PR B: TranslationOperator (#30, merged) — Issue #21
  - PR C: LogCoordinates (#31, merged) — Issue #22
  - PR D: SupportDisjointness (#32, merged) — Issue #23
  - PR E: PrimeDistribution (#33, merged) — Issue #24
  - PR F: ArchimedeanWeight (#34, merged) — Issue #25
  - PR G: ArchimedeanDistribution (#35, merged) — Issue #26
  - PR H: EnergyForm (#36, merged) — Issue #27, 0 sorries
- CI sorry regression check added (grep -rnw in CI, blocks merge)
- All Stage 2 files so far have **0 sorries**
- **Stage 4**: Complete. All 5 PRs merged.
  - PR A: NormalContraction (#45, merged) — Issue #40
  - PR B: MarkovProperty (#46, merged) — Issue #41
  - PR C: TranslationInvariance (#47, merged) — Issue #42
  - PR D: MollificationConstancy (#48, merged) — Issue #43
  - PR E: NullOrConull (#49, merged) — Issue #44
- **Stage 5**: Complete. All 5 PRs merged, 0 sorries, 9 axioms.
  - PR A: FourierSymbol (#55, merged) — Issue #50
  - PR B: SymbolLowerBound (#56, merged) — Issue #51
  - PR C: ClosedForm (#57, merged) — Issue #52
  - PR D: CompactEmbedding (#58, merged) — Issue #53
  - PR E: CompactResolvent (#60, merged) — Issue #54
- **Stage 6**: Redo planned. Previous PRs (#66-#70) will be superseded.
  - Issues: #61 (6A), #62 (6B), #63 (6C), #64 (6D), #65 (6E)
  - **Redo all 5 files from scratch** with proper discipline:
    1. Plan each file → get user review → then implement
    2. Write in 100-150 line chunks, diagnostics after each
    3. Don't move to next file until current is clean and user has seen it
  - Previous lessons: 6A lacked plan review, 6B had too many errors, 6D blew context (800 lines in one shot)
- **Axiom elimination roadmap**: `docs/axiom-elimination-roadmap.md` — 6 project docs written
  - 9 of 10 axioms eliminable (~760 lines), kato_operator stays as axiom
  - Plancherel already in Mathlib (`norm_fourier_eq`), DomMulAct for L² continuity

## Workflow
- **One PR per session**, push for Copilot review, wait for user approval, then merge
- Each PR branch from main, target main
- Don't use `--delete-branch` on merge (caused #29 to auto-close)
- **Include tests in every PR** — don't batch tests into a separate final PR
- Use plan → **get user review of plan** → MCP API verification → implement pipeline for each PR
- **Never skip plan review.** 6A failed because plan wasn't reviewed. Always present the plan and wait for approval before implementing.
- **CRITICAL: Write Lean files in ~100-150 line chunks**, checking `lean_diagnostic_messages` after each chunk. Fix errors before writing the next chunk. Never write >200 lines without a diagnostics check. Large files written in one shot cause cascading errors that eat the context window across session boundaries.

## Style Preferences
- **Prefer Mathlib lemmas over manual proofs** — more eyes have reviewed that code
- When a Mathlib lemma exists (even if it needs a `simpa` rewrite), use it over hand-rolling

## Naming Convention
- Use `cutoffLambda` (not `λ`, `Λ`, or `Lam`) for the cutoff parameter
  - `λ` is reserved keyword in Lean 4
  - `Λ` (capital Lambda) is visually identical to `∧` (And) — humans can't see the difference
  - `cutoffLambda` is self-documenting: says what it is and what paper symbol it represents

## Key Learnings
- See [lean-patterns.md](lean-patterns.md) for Lean/LSpec gotchas
- See [ci-notes.md](ci-notes.md) for CI and repo structure notes
- See [sorry-tracker.md](sorry-tracker.md) for sorry proof history (all closed)
- See [review-lessons.md](review-lessons.md) for planning and review process lessons
- `Set.indicator_of_notMem` (not `indicator_of_not_mem`) in current Mathlib
- For `lintegral_add_left`, need explicit measurability: `h_meas.nnnorm.coe_nnreal_ennreal.pow_const _`
- See [lean-patterns.md](lean-patterns.md) § "Lean 4 parsing quirks" for `let`/negation and `∂volume` issues
- `mul_sub_le_image_sub_of_le_deriv` is the key MVT lemma for bounding special functions
- `field_simp` handles exp cancellation (`exp(-t/2) * exp(t/2) = 1`) better than manual `rw` chains
- Don't defer to `sorry` when proof is likely within reach — adds commit churn and review cycles
- Use `refine` (not `apply`) when lemma has mixed term/prop arguments (e.g. `IntegrableOn.of_bound`)

## Environment
- `lake` requires `export PATH="$HOME/.elan/bin:$PATH"` in Codespaces
- Lean toolchain: v4.28.0, Mathlib v4.28.0
- lean-lsp MCP server configured (`.mcp.json`), verified working — provides goal state, diagnostics, lemma search, multi-attempt tactics
