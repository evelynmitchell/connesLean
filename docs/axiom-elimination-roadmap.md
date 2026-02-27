# Axiom Elimination Roadmap

## Overview

ConnesLean currently uses **10 axioms** across Stages 2, 5, and 6. This document
maps each axiom to a formalization project, prioritized by feasibility and
Mathlib contribution value.

## Axiom Inventory

| # | Axiom | File | Stage | Feasibility | Project Doc |
|---|---|---|---|---|---|
| 1 | `translation_norm_sq_continuous` | TranslationOperator.lean | 2 | **Easy** | [L² Strong Continuity](project-l2-strong-continuity.md) |
| 2 | `fourierSymbol_ge_log` | SymbolLowerBound.lean | 5B | **Medium** | [Fourier Symbol Lower Bound](project-fourier-symbol-lower-bound.md) |
| 3 | `frequency_moment_control` | SymbolLowerBound.lean | 5B | **Easy** | [Fourier Symbol Lower Bound](project-fourier-symbol-lower-bound.md) |
| 4 | `energyForm_eq_fourierSymbol_integral` | ClosedForm.lean | 5C | **Medium** | [Plancherel Bridge](project-plancherel-bridge.md) |
| 5 | `formDomain_eq_weighted_fourier` | ClosedForm.lean | 5C | **Medium** | [Plancherel Bridge](project-plancherel-bridge.md) |
| 6 | `energyForm_closed_on_line` | ClosedForm.lean | 5C | **Hard** | [Plancherel Bridge](project-plancherel-bridge.md) |
| 7 | `energyForm_closed_on_interval` | ClosedForm.lean | 5C | **Medium** | [Plancherel Bridge](project-plancherel-bridge.md) |
| 8 | `kolmogorov_riesz_compact` | CompactEmbedding.lean | 5D | **Medium** | [Kolmogorov-Riesz](project-kolmogorov-riesz.md) |
| 9 | `formNormBall_equicontinuous` | CompactEmbedding.lean | 5D | **Hard** | [Form-Norm Equicontinuity](project-formNormBall-equicontinuity.md) |
| 10 | `kato_operator` | CompactResolvent.lean | 5E | **Extreme** | [Kato Representation](project-kato-representation.md) |

## Project Summary

### Tier 1: Ready Now (Mathlib has the infrastructure)

| Project | Axioms Eliminated | Lines | Key Insight |
|---|---|---|---|
| [L² Strong Continuity](project-l2-strong-continuity.md) | 1 | ~60 | Mathlib's `DomMulAct` already provides this |
| [Fourier Symbol Lower Bound](project-fourier-symbol-lower-bound.md) | 2 | ~115 | Pure integral estimation, all building blocks exist |

**Total: 3 axioms, ~175 lines**

### Tier 2: Achievable (Mathlib has partial infrastructure)

| Project | Axioms Eliminated | Lines | Key Insight |
|---|---|---|---|
| [Plancherel Bridge](project-plancherel-bridge.md) | 4 | ~210 | Mathlib has Plancherel! Need bridge to concrete integrals |
| [Kolmogorov-Riesz](project-kolmogorov-riesz.md) | 1 | ~175 | Arzelà-Ascoli + mollification; no deep dependencies |

**Total: 5 axioms, ~385 lines**

### Tier 3: Major Infrastructure Project

| Project | Axioms Eliminated | Lines | Key Insight |
|---|---|---|---|
| [Form-Norm Equicontinuity](project-formNormBall-equicontinuity.md) | 1 | ~200 | Depends on Plancherel Bridge (Tier 2) completing first |

**Total: 1 axiom, ~200 lines (after Tier 2)**

### Tier 4: Keep as Axiom

| Project | Axioms | Why |
|---|---|---|
| [Kato Representation](project-kato-representation.md) | 1 | Requires ~2500 lines of new Mathlib infrastructure (unbounded operators, spectral theory) |

## Recommended Execution Order

```
Phase 1 (Quick Wins):
  ├── L² Strong Continuity .......... 1 axiom, ~60 lines
  └── Fourier Symbol Lower Bound .... 2 axioms, ~115 lines
                                       ─────────────────
                                       3 axioms eliminated

Phase 2 (Bridge Projects):
  ├── Plancherel Bridge ............. 4 axioms, ~210 lines
  └── Kolmogorov-Riesz .............. 1 axiom, ~175 lines
                                       ─────────────────
                                       5 axioms eliminated

Phase 3 (Depends on Phase 2):
  └── Form-Norm Equicontinuity ...... 1 axiom, ~200 lines
                                       ─────────────────
                                       1 axiom eliminated

                                Total: 9 of 10 axioms eliminated
                                       ~760 lines of new code
                                Remaining: kato_operator (keep as axiom)
```

## Dependency Graph

```
                    ┌──────────────────────────┐
                    │   Kato Representation     │
                    │   (keep as axiom)         │
                    └──────────────────────────┘

  ┌─────────────────┐     ┌──────────────────────┐
  │ L² Strong       │     │ Fourier Symbol       │
  │ Continuity      │     │ Lower Bound          │
  │ (1 axiom)       │     │ (2 axioms)           │
  └─────────────────┘     └──────────┬───────────┘
                                     │ uses fourierSymbol_ge_log
                                     ▼
                          ┌──────────────────────┐
                          │ Plancherel Bridge    │
                          │ (4 axioms)           │
                          └──────────┬───────────┘
                                     │ enables Fourier rep
                    ┌────────────────┤
                    │                │
                    ▼                ▼
  ┌─────────────────┐     ┌──────────────────────┐
  │ Kolmogorov-     │     │ Form-Norm            │
  │ Riesz           │     │ Equicontinuity       │
  │ (1 axiom)       │     │ (1 axiom)            │
  │ [independent]   │     │ [needs Plancherel]    │
  └─────────────────┘     └──────────────────────┘
```

## Mathlib Contribution Value

Each project is rated for its value as a standalone Mathlib PR:

| Project | Mathlib Value | Reusability |
|---|---|---|
| L² Strong Continuity | Medium | Bridge lemmas (snorm ↔ lintegral) |
| Fourier Symbol Lower Bound | **High** | sin²/u integral bound is a fundamental estimate |
| Plancherel Bridge | **High** | Fourier-of-translation identity is fundamental |
| Kolmogorov-Riesz | **Very High** | Major missing theorem in functional analysis |
| Form-Norm Equicontinuity | Medium | Specific to energy form context |
| Kato Representation | **Extremely High** | Would unblock all unbounded operator theory |

The Kolmogorov-Riesz theorem and the sin²/u integral bound would be the
most impactful standalone Mathlib contributions.

## Stage 6 Axioms (Future)

Stages 6B and 6E (not yet implemented) will introduce 3 additional axioms:
- `laplace_resolvent_commute` (6B) — Bochner integral of semigroup
- `projection_commutes_with_sqrt` (6B) — Borel functional calculus
- `closed_ideal_classification` (6E) — Banach lattice theory

These are deep functional analysis results that will likely remain as axioms,
similar to `kato_operator`.
