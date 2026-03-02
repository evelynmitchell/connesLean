# ConnesLean Project Memory

## Project Summary (Complete)
Formalization in Lean 4 + Mathlib of Christopher Long's proof of properties of the
Restricted Weil Quadratic Form, from LaTeX structured proofs (lamportform.tex) to
verified Lean code. 8 stages, ~30 Lean files, 14 axioms, 0 sorries, full CI pipeline
with soundness auditing. Covers: multiplicative Haar measure, dilation/convolution operators,
energy decomposition, Markov/translation-invariance, Fourier analysis, compact resolvent,
semigroup irreducibility, Perron-Frobenius ground state, and inversion symmetry (even eigenfunction).

## Project State
- **Stage 1**: Complete. All 9 sorries closed, PRs #9-#18 merged.
- **Stage 2**: Complete. 8 PRs merged, 0 sorries (PRs #28-#36, Issues #19-#27).
- CI sorry regression check added (grep -rnw in CI, blocks merge)
- **Stage 4**: Complete. 5 PRs merged (PRs #45-#49, Issues #40-#44).
- **Stage 5**: Complete. 5 PRs merged, 0 sorries, 9 axioms (PRs #55-#60, Issues #50-#54).
- **Stage 6**: Re-split into 8 files. Previous code reverted, old issues closed.
  - **#71 (6A-i IndicatorEnergy)**: Done. PR #78, merged.
  - **#72 (6A-ii EnergyPositivity)**: Done. PR #89, merged.
  - **#62 (6B InvarianceSplit)**: Done. PR #91, merged. Renamed to `EnergyFormSplit` with dot-notation theorems (`inv.domain_preserved`, `inv.split`).
  - **#73 (6C ConstantInDomain)**: Done. PR #93. 276L, 0 sorries, 0 axioms. Key: `constant_in_formDomain`, `splitting_applied_to_constant`, `indicator_complement_sum/disjoint`.
  - **#74 (6D-i NormInequality)**: Done. PR #96. 344L, 0 sorries, 0 axioms. Key: `nnnorm_sq_indicator_ge` (9-case pointwise), `energyForm_indicator_add_ge`.
  - **#75 (6D-ii EnergyEquality)**: Done. PR #97. 347L, 0 sorries, 0 axioms. Key: `archEnergyIntegral_indicator_eq`, `inner_integral_indicator_everywhere_eq`. Uses `innerIntegral` private def, `ae_eq_of_ae_le_of_lintegral_le`, `Measure.eqOn_of_ae_eq`.
  - **#76 (6D-iii CrossVanishing)**: Done. PR #99. 265L, 0 sorries, 0 axioms. Key: `nnnorm_sq_indicator_ae_eq`, `indicator_B_ae_invariant`, `indicator_translation_invariant_of_split`, `invariant_ideal_null_or_conull`.
  - **#77 (6E Irreducibility)**: Done. PR #100, merged. 131L, 0 sorries, 1 axiom (`closed_ideal_classification`).
  - Chain: #71 → #72 → #73 → #74 → #75 → #76 → #77, with #62 → #73
  - `innerIntegral` made public in EnergyEquality.lean (PR #97) for downstream use
  - Discipline: plan → user review → implement in 100-150 line chunks
- **Stage 7**: PR #101, merged. 175L, 0 sorries, 13 axioms total (11 → 13).
  - `IsPositivityImproving` def, `GroundState` structure (7 fields)
  - 2 new axioms: `semigroup_positivity_improving`, `ground_state_simple`
  - Main result: `ground_state_exists` (def, not theorem — GroundState is data, not Prop)
- **Stage 8**: PR #102, merged. 217L, 0 sorries, 14 axioms total (13 → 14).
  - 1 new axiom: `resolvent_commutes_reflection` (Proposition 14)
  - Key defs: `reflectionOp`, `ae_neg`, `ae_of_ae_neg`, `logInterval_neg_mem`
  - Main result: `ground_state_even` — ψ(-u) = ψ(u) a.e. (Corollary 16)
  - Proof: R(ψ) eigenfunction → simplicity → c·ψ → c²=1 → c≠-1 by positivity → c=1
  - ae_neg uses `Real.volume_preimage_mul_left` (not `IsNegInvariant` which lacks instance)
- **Axiom elimination roadmap**: `docs/axiom-elimination-roadmap.md`
  - 9 of 10 axioms eliminable (~760 lines), kato_operator stays as axiom
- **Axiom soundness lint**: PR #92, merged. `scripts/lint_axiom_soundness.sh` enforces `**Soundness:**` annotations + inventory sync. CI step added. `ConnesLeanTest/SoundnessTests.lean` has 7 executable cross-checks. `docs/axiom-soundness-convention.md` documents the convention.

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
