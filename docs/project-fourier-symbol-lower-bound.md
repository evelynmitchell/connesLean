# Project: Prove `fourierSymbol_ge_log` and `frequency_moment_control`

## Goal

Replace the two axioms in `ConnesLean/ConnesLean/Stage5/SymbolLowerBound.lean`
with fully proved theorems, eliminating 2 axioms from the formalization.

## Current Axioms

### 1. `fourierSymbol_ge_log` (line 146)

```lean
axiom fourierSymbol_ge_log (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∃ ξ₀ : ℝ, 2 ≤ ξ₀ ∧
      ∀ ξ : ℝ, ξ₀ ≤ |ξ| → c₁ * Real.log |ξ| - c₂ ≤ fourierSymbol cutoffLambda ξ
```

The Fourier symbol `ψ_λ(ξ)` grows at least logarithmically for large `|ξ|`.

### 2. `frequency_moment_control` (line 163)

```lean
axiom frequency_moment_control (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ ξ : ℝ, Real.log (2 + |ξ|) ≤ a + b * fourierSymbol cutoffLambda ξ
```

`log(2 + |ξ|) ≤ a + b · ψ_λ(ξ)` — the symbol controls a logarithmic moment.

## Mathematical Source

`lamportform.tex`:
- **Lemma 11** (lines 964–1021): proof of `fourierSymbol_ge_log`
- **Corollary 12** (lines 1023–1057): proof of `frequency_moment_control`

## Proof Outline

### `fourierSymbol_ge_log` (Lemma 11)

**Step 1: Reduce to archimedean integral.**
Drop the nonneg prime sum from the Fourier symbol. The archimedean integral
alone gives a lower bound:

```
ψ_λ(ξ) ≥ ∫₀^{2L} w(t) · 4sin²(ξt/2) dt
```

**Step 2: Lower bound the weight.**
Use the existing theorem `archWeight_ge_inv_two_t` (Stage 2F):

```
w(t) ≥ c₀ / t   for t ∈ (0, min(1, 2L))
```

This gives (for `t₀ = min(1, 2L)`):

```
ψ_λ(ξ) ≥ 4c₀ ∫₀^{t₀} (1/t) sin²(ξt/2) dt
```

**Step 3: Substitution `u = ξt/2`.**
For `|ξ| ≥ 2`:

```
∫₀^{t₀} (1/t) sin²(ξt/2) dt = ∫₀^{|ξ|t₀/2} (1/u) sin²(u) du
```

**Step 4: Harmonic-series lower bound.**
Partition `[0, R]` (where `R = |ξ|t₀/2`) into intervals `[kπ, (k+1)π]`.
On each full interval:

```
∫_{kπ}^{(k+1)π} sin²(u)/u du ≥ (1/((k+1)π)) · ∫₀^π sin²(u) du = 1/(2(k+1))
```

Summing over `k = 0, ..., N-1` where `N = ⌊R/π⌋`:

```
∫₀^R sin²(u)/u du ≥ (1/2) Σ_{k=1}^{N} 1/k ≥ (1/2) log(N)
```

**Step 5: Assemble.**
With `N ~ |ξ| t₀ / (2π)`:

```
ψ_λ(ξ) ≥ 4c₀ · (1/2) · log(|ξ| t₀ / (2π))
       = 2c₀ · (log|ξ| + log(t₀/(2π)))
       = 2c₀ · log|ξ| - 2c₀ · |log(t₀/(2π))|
```

Set `c₁ = 2c₀`, `c₂ = 2c₀ · |log(t₀/(2π))|`, `ξ₀ = max(2, 2π/t₀)`.

### `frequency_moment_control` (Corollary 12)

This follows directly from `fourierSymbol_ge_log`:

- For `|ξ| ≥ ξ₀`: rearrange `c₁ log|ξ| - c₂ ≤ ψ_λ(ξ)` to get
  `log(2+|ξ|) ≤ log(3|ξ|) ≤ (ψ_λ(ξ) + c₂)/c₁ + log 3`.
- For `|ξ| < ξ₀`: `log(2+|ξ|) ≤ log(2+ξ₀)`, a finite constant.
- Set `b = 1/c₁`, `a = c₂/c₁ + log 3 + log(2+ξ₀)`.

## What Mathlib Provides

| Component | Mathlib Status | Reference |
|---|---|---|
| `∫ sin²(u) du = π/2` on `[0,π]` | ⚠️ Partial — `integral_sin_sq` may exist | Need to check |
| `sin²(u)/u` integral bounds | ❌ Not directly | Need to build |
| Harmonic series lower bound | ✅ Available | `Real.log_le_sum_inv` or similar |
| `log(ab) = log a + log b` | ✅ Available | `Real.log_mul` |
| Substitution `u = ct` in integrals | ✅ Available | `MeasureTheory.integral_comp_mul_right` |
| `archWeight_ge_inv_two_t` | ✅ In ConnesLean | Stage 2F |
| `fourierSymbol` definition | ✅ In ConnesLean | Stage 5A |

## What Needs to Be Built

### A. sin²/u Integral Lower Bound (~40 lines)

The key technical lemma: for `R ≥ π`:

```lean
theorem integral_sin_sq_div_ge_log (R : ℝ) (hR : π ≤ R) :
    (1/2) * Real.log (R / π) ≤ ∫ u in Set.Icc 0 R, Real.sin u ^ 2 / u
```

**Proof:** Partition into `[kπ, (k+1)π]` intervals, bound `1/u ≥ 1/((k+1)π)`,
use `∫₀^π sin² = π/2`, sum the harmonic series.

### B. Substitution and Assembly for `fourierSymbol_ge_log` (~50 lines)

- Substitute `u = ξt/2` in the archimedean integral
- Apply the sin²/u bound
- Assemble with `archWeight_ge_inv_two_t`

### C. `frequency_moment_control` from `fourierSymbol_ge_log` (~25 lines)

Case split on `|ξ| ≥ ξ₀` vs `|ξ| < ξ₀`, rearrange inequalities.

## Estimated Effort

| Component | Lines | Difficulty |
|---|---|---|
| sin²/u integral bound (A) | ~40 | Hard |
| Substitution + assembly (B) | ~50 | Medium |
| Moment control from log bound (C) | ~25 | Easy |
| **Total** | **~115** | |

## Dependencies

- **Internal:** `archWeight_ge_inv_two_t` (Stage 2F, already proved)
- **Internal:** `fourierSymbol` definition (Stage 5A, already proved)
- **No dependency on Plancherel or other axioms**
- `frequency_moment_control` depends on `fourierSymbol_ge_log` (prove in order)

## Files to Create/Modify

- **New:** `ConnesLean/ConnesLean/Analysis/SinSqIntegral.lean` — the sin²/u bound
- **Modify:** `Stage5/SymbolLowerBound.lean` — replace both axioms with theorems

## Risks and Mitigations

| Risk | Mitigation |
|---|---|
| Integral manipulation in Lean is painful | Use `MeasureTheory.integral_comp_mul_right` for substitution |
| Partitioning `[0,R]` into π-intervals is fiddly | Define helper `intervalPartition` for clarity |
| Harmonic series lower bound API may not exist | Can prove `Σ 1/k ≥ log(N)` directly (~15 lines) |
| The constant tracking (c₁, c₂, ξ₀) is tedious | Use `obtain` destructuring and `linarith`/`nlinarith` |

## Mathlib Contribution Potential

**High.** The lemma `∫₀^R sin²(u)/u du ≥ (1/2) log(R/π)` is a fundamental
estimate in harmonic analysis with applications beyond this project (e.g.,
Dirichlet kernel analysis, signal processing). The harmonic-series-via-sin²
approach is elegant and reusable.

## Success Criteria

- Both axioms in `SymbolLowerBound.lean` replaced by theorems
- `lean_verify` shows no dependency on the old axioms
- `lake build` passes with 0 errors, 0 sorries
- Downstream files (`ClosedForm.lean`, `CompactEmbedding.lean`) still compile
