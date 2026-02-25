# Stage 3: Energy Decomposition — Completion Report

## Summary

Stage 3 formalized the energy decomposition of local explicit-formula terms into
translation-difference energies, covering Section 4 of `lamportform.tex` (lines 251–470).
This stage was implemented across 8 PRs within the `Stage2/` directory, since the plan
and file structure were established before the stage numbering was finalized.

**Status:** Core energy-form infrastructure complete (Issue #3 closed 2026-02-25). **0 sorries.**
The assembly theorems `lem:prime-energy` and `lem:arch-energy` are specified but
intentionally deferred (see "Deferred work").

## Scope

- **Lemma 3** (prime energy, `lem:prime-energy` — specification only): Target
  decomposition expressing −W_p(f) as a sum of ‖G̃ − S_{m log p} G̃‖² terms plus
  c_p(λ)‖G‖². The Lean development formalizes the translation-difference energy terms
  and constants on the right-hand side; the full equivalence with −W_p(f) is deferred.
- **Lemma 4** (archimedean energy, `lem:arch-energy` — specification only): Target
  decomposition expressing −W_R(f) as ∫₀^{2L} w(t) ‖G̃ − S_t G̃‖² dt + c_∞(λ)‖G‖².
  The Lean development formalizes the energy-form side and constants; the assembly
  theorem relating this to −W_R(f) is deferred.
- **Definition 5** (`def:E` — fully formalized): The difference-energy form E_λ(G)
  combining the archimedean integral and prime sums, implemented in `EnergyForm.lean`
  together with its basic properties (nonnegativity, zero-at-zero, and assembly
  from the prime and archimedean contributions).

## Files

All files live under `ConnesLean/ConnesLean/Stage2/`:

| File | Description | PR |
|------|-------------|----|
| `TranslationOperator.lean` | S_t on L²(ℝ), dilation↔translation correspondence | #30 |
| `LogCoordinates.lean` | L² isometry exp/log, zero-extension, interval I | #31 |
| `SupportDisjointness.lean` | Disjoint support → orthogonality, Remark 2 truncation | #32 |
| `PrimeDistribution.lean` | Prime bounds/finsets, primeConstant, prime energy terms | #33 |
| `ArchimedeanWeight.lean` | w(t) = e^{t/2}/(2 sinh t), pointwise bounds, integrability | #34 |
| `ArchimedeanDistribution.lean` | W_R(f) definition, archimedean energy constants | #35 |
| `EnergyForm.lean` | E_λ(G) and totalCorrection definitions, sum of energy pieces, basic lemmas | #36 |

The `rpDivEquiv` refactor (PR #28) was a prerequisite extraction from Stage 1.

## PRs (in merge order)

| PR | Title | Merged |
|----|-------|--------|
| #28 | Extract rpDivEquiv and measurePreserving_rpDiv (Issue #19) | 2026-02-24 |
| #30 | Add TranslationOperator.lean (Issue #21) | 2026-02-24 |
| #31 | Add LogCoordinates.lean (Issue #22) | 2026-02-24 |
| #32 | Add SupportDisjointness.lean (Issue #23) | 2026-02-24 |
| #33 | Add PrimeDistribution.lean (Issue #24) | 2026-02-24 |
| #34 | Archimedean weight and pointwise bounds (Issue #25) | 2026-02-24 |
| #35 | Add ArchimedeanDistribution W_R(f) (Issue #26) | 2026-02-25 |
| #36 | Add EnergyForm E_λ(G) (Issue #27) | 2026-02-25 |

## Key design decisions

1. **`cutoffLambda` naming**: Used `cutoffLambda` (not `λ`, `Λ`, or `Lam`) for the cutoff
   parameter — `λ` is a Lean keyword and `Λ` is visually indistinguishable from `∧` (And).

2. **Plain functions first**: All distributions (W_p, W_R) and operators (S_t) defined as
   plain functions, with Lp/integrability properties proved as separate lemmas.

3. **Set.indicator for zero-extension**: Implemented G̃ (zero-extension outside interval I)
   via `Set.indicator` to leverage Mathlib's indicator lemmas.

4. **Finset construction from real bounds**: Used `Nat.floor` with helper functions
   (`primeBound`, `primeExponentBound`) to convert real-valued bounds (p ≤ λ², p^m ≤ λ²)
   into `Finset` ranges for the double sum.

5. **Integrability-first proof structure**: Lean requires `Integrable` hypotheses before
   `integral_add`/`integral_sub`, so proofs were restructured from the LaTeX ordering to
   establish all integrability before any integral rearrangement.

## Deferred work

Issue #37 (open, low priority) tracks two assembly theorems:
- `lem:prime-energy`: Full proof connecting W_p(f) to the prime energy term in E_λ
- `lem:arch-energy`: Full proof connecting W_R(f) to the archimedean energy integral

These require a measure-preserving promotion for `logCoordL2Equiv` and ENNReal/ℝ/ℂ type
bridging at the integration boundary. They are **not blocking** forward progress — the paper
(lines 446–456) states all subsequent arguments (Stages 4–8) use only the abstract properties
of E_λ, not its decomposition into prime/archimedean pieces.

## Dependencies

- **Blocked by:** Stage 1 (complete, 0 sorries), Stage 2 plan (PR #20)
- **Blocks:** Stage 4 (Markov property), Stage 5 (Fourier analysis), Stage 6 (Irreducibility)

## Verification

- `lake build ConnesLean` compiles without errors
- `grep -rn sorry ConnesLean/ConnesLean/Stage2/` returns no results
- CI sorry regression check passes on all merged PRs
