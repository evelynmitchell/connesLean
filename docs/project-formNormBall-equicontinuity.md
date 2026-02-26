# Project: Prove `formNormBall_equicontinuous`

## Goal

Replace the axiom `formNormBall_equicontinuous` in
`ConnesLean/ConnesLean/Stage5/CompactEmbedding.lean` (line 71) with a
fully proved theorem, eliminating one axiom from the formalization.

## Current Axiom

```lean
axiom formNormBall_equicontinuous (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (M : ENNReal) (hM : M < ⊤) :
    ∀ ε : ENNReal, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ φ ∈ formNormBall cutoffLambda M, ∀ h : ℝ,
        |h| < δ → (∫⁻ u, ‖φ (u - h) - φ u‖₊ ^ (2 : ℝ)) < ε
```

This says: the form-norm ball (functions with compact support in I and
bounded graph norm ‖φ‖² + E_λ(φ) ≤ M) satisfies L²-translation
equicontinuity — for any ε > 0 there exists a uniform δ > 0 working
for all φ in the ball simultaneously.

## Mathematical Source

`lamportform.tex`, Lemma 13 (lines 1078–1127).

## Proof Outline

The proof splits the translation difference into low and high frequency
parts using Plancherel, then bounds each part separately.

### Step 1: Plancherel for Translation Differences

For any φ ∈ L² and h ∈ ℝ:

```
‖φ(· − h) − φ‖₂² = (1/2π) ∫_ℝ 4 sin²(ξh/2) |φ̂(ξ)|² dξ
```

This identity converts the spatial translation difference into a
frequency-domain integral with the weight `4 sin²(ξh/2)`.

### Step 2: Frequency Splitting at Threshold R ≥ 1

Split the integral at `|ξ| = R`:

**Low frequency** (`|ξ| ≤ R`):
```
∫_{|ξ|≤R} 4 sin²(ξh/2) |φ̂(ξ)|² dξ
  ≤ (Rh)² · ∫_ℝ |φ̂(ξ)|² dξ        [since sin²(x) ≤ x²]
  = (Rh)² · 2π ‖φ‖₂²                [Plancherel]
  ≤ (Rh)² · 2πM                      [‖φ‖₂² ≤ M from form-norm bound]
```

**High frequency** (`|ξ| > R`):
```
∫_{|ξ|>R} 4 sin²(ξh/2) |φ̂(ξ)|² dξ
  ≤ 4 ∫_{|ξ|>R} |φ̂(ξ)|² dξ                    [sin² ≤ 1]
  ≤ (4/log(2+R)) ∫_ℝ log(2+|ξ|) |φ̂(ξ)|² dξ    [log(2+|ξ|) ≥ log(2+R) on domain]
```

### Step 3: Frequency Moment Control

The integral `∫ log(2+|ξ|) |φ̂(ξ)|² dξ` is controlled by the
`frequency_moment_control` axiom (Stage 5B, Corollary 12):

```
log(2 + |ξ|) ≤ a + b · ψ_λ(ξ)
```

Combined with the Fourier representation of the energy form
(`energyForm_eq_fourierSymbol_integral`, Stage 5C):

```
∫ log(2+|ξ|) |φ̂(ξ)|² dξ ≤ a · ‖φ‖₂² + b · E_λ(φ) ≤ (a+b) · M
```

where the last step uses `‖φ‖₂² + E_λ(φ) ≤ M` from the form-norm bound.

### Step 4: Combine and Choose Parameters

Putting it together:

```
‖φ(· − h) − φ‖₂² ≤ (Rh)² · C₁(M) + C₂(M) / log(2+R)
```

Given ε > 0:
1. Choose R large enough that `C₂(M) / log(2+R) < ε/2`
2. Choose δ = √(ε / (2 · R² · C₁(M))) so that `(Rδ)² · C₁(M) < ε/2`
3. For |h| < δ: both terms < ε/2, so the total < ε

## What Mathlib Provides

| Component | Mathlib Status | Reference |
|-----------|---------------|-----------|
| Fourier transform definition | ✅ Available | `FourierTransform.fourier` |
| Plancherel theorem ‖f̂‖₂ = ‖f‖₂ | ❌ Not available | **The main blocker** |
| sin² ≤ x² bound | ✅ Available | `Real.sin_le_abs` or similar |
| sin² ≤ 1 bound | ✅ Available | `sin_sq_le_one` |
| log monotonicity | ✅ Available | `Real.log_le_log` |
| Basic ε-δ arithmetic | ✅ Available | `div_pos`, `mul_lt_mul`, etc. |

## What Needs to Be Built

### Prerequisite: Plancherel Theorem (~100–150 lines)

This is the critical dependency. Plancherel states:

```
‖f̂‖_{L²} = ‖f‖_{L²}
```

or equivalently, the Fourier transform extends to a unitary operator on L².

**Proof strategy for Plancherel**:
1. Prove Parseval for Schwartz functions (using Fourier inversion +
   dominated convergence)
2. Schwartz functions are dense in L² (Mathlib may have density results)
3. Extend by density to all of L²

**Alternative**: Axiomatize Plancherel as a single, clean, reusable axiom
and prove everything else from it. This is honest about the gap and
keeps the axiom surface minimal.

**Note**: Plancherel is also needed by `energyForm_eq_fourierSymbol_integral`
(ClosedForm.lean) and `energyForm_closed_on_line` (ClosedForm.lean).
Proving Plancherel would unblock multiple axioms simultaneously.

### A. Translation Difference Identity (~20 lines)

```
‖φ(· − h) − φ‖₂² = (1/2π) ∫ 4 sin²(ξh/2) |φ̂(ξ)|² dξ
```

Proof: expand `|φ̂(· − h)(ξ) − φ̂(ξ)|²`, use `φ̂(· − h)(ξ) = e^{−ihξ} φ̂(ξ)`,
simplify `|e^{−ihξ} − 1|² = 4 sin²(hξ/2)`, apply Plancherel.

### B. Low-Frequency Bound (~15 lines)

```
∫_{|ξ|≤R} 4 sin²(ξh/2) |φ̂(ξ)|² dξ ≤ (Rh)² · 2π · M
```

Uses `sin(x) ≤ |x|` and restriction of integral domain.

### C. High-Frequency Bound (~20 lines)

```
∫_{|ξ|>R} |φ̂(ξ)|² dξ ≤ (1/log(2+R)) · ∫ log(2+|ξ|) |φ̂(ξ)|² dξ
```

Uses `log(2+|ξ|) ≥ log(2+R)` for `|ξ| > R` to divide out.

### D. Moment Bound from Form Norm (~15 lines)

```
∫ log(2+|ξ|) |φ̂(ξ)|² dξ ≤ C(a,b) · M
```

Combines `frequency_moment_control` with `energyForm_eq_fourierSymbol_integral`
and the form-norm bound.

### E. ε-δ Assembly (~20 lines)

Choose R, then δ, verify both halves are < ε/2.

## Dependency Graph

```
Plancherel ──────────────────────────┐
  (NOT in Mathlib)                   │
                                     ▼
frequency_moment_control ──► Moment bound (D)
  (axiom, Stage 5B)                  │
                                     ▼
energyForm_eq_fourierSymbol_integral─► High-freq bound (C)
  (axiom, Stage 5C)                  │
                                     ▼
                        Translation identity (A) + Low-freq (B)
                                     │
                                     ▼
                        formNormBall_equicontinuous
```

**Key observation**: This proof depends on TWO other axioms:
- `frequency_moment_control` (Stage 5B)
- `energyForm_eq_fourierSymbol_integral` (Stage 5C)

Both of those also depend on Plancherel. So proving Plancherel would
potentially unblock three axioms at once.

## Estimated Effort

| Component | Lines | Depends on Plancherel? |
|-----------|-------|----------------------|
| Plancherel theorem | 100–150 | — |
| Translation identity (A) | 20 | Yes |
| Low-frequency bound (B) | 15 | Yes (indirectly via A) |
| High-frequency bound (C) | 20 | Yes (indirectly via moment) |
| Moment bound (D) | 15 | Yes (via energy form representation) |
| ε-δ assembly (E) | 20 | No |
| **Total** | **~200–250** | |

Without Plancherel (axiomatizing it instead): ~70 lines for B–E.

## Recommended Approach

### Option 1: Prove Plancherel First (Recommended if Going Deep)

Plancherel is the single biggest blocker across the entire project.
It gates this axiom, `energyForm_eq_fourierSymbol_integral`, and
`energyForm_closed_on_line`. Proving it once unblocks three things.

Estimated effort: 100–150 lines for a self-contained Plancherel proof,
plus the 70 lines for this theorem.

### Option 2: Axiomatize Plancherel, Prove This Theorem

Replace the current axiom with a cleaner, more fundamental one:

```lean
axiom plancherel (f : ℝ → ℂ) (hf : Integrable f) :
    ∫⁻ ξ, ‖FourierTransform.fourier f ξ‖₊ ^ (2 : ℝ) =
    (2 * Real.pi) • ∫⁻ u, ‖f u‖₊ ^ (2 : ℝ)
```

Then prove `formNormBall_equicontinuous` from Plancherel + the existing
axioms. This reduces the axiom surface (one clean Plancherel axiom
replacing multiple ad-hoc ones) while being honest about the gap.

Estimated effort: ~70 lines for the equicontinuity proof.

## Files to Create/Modify

### Option 1 (Full Plancherel)
- **New file**: `ConnesLean/ConnesLean/Analysis/Plancherel.lean`
- **Modify**: `CompactEmbedding.lean` — import Plancherel, replace axiom
- **Potentially modify**: `ClosedForm.lean` — replace its Plancherel-dependent
  axioms too

### Option 2 (Axiomatize Plancherel)
- **New file**: `ConnesLean/ConnesLean/Analysis/Plancherel.lean` (just the axiom)
- **Modify**: `CompactEmbedding.lean` — prove equicontinuity from Plancherel axiom

## Risks and Mitigations

| Risk | Mitigation |
|------|-----------|
| Plancherel proof is long and hard | Option 2 axiomatizes it cleanly |
| `frequency_moment_control` is also an axiom | Accept the dependency; that's a separate project |
| Fourier transform API in Mathlib is thin | May need measurability/integrability lemmas |
| ENNReal vs ℝ arithmetic is painful | Use `toReal` conversions carefully; follow patterns in ClosedForm.lean |

## Success Criteria

- `formNormBall_equicontinuous` is a `theorem`, not an `axiom`
- `lean_verify` shows no dependency on the old axiom
- If Option 2: only depends on a clean Plancherel axiom (+ existing axioms)
- If Option 1: no Plancherel axiom at all
- `lake build` passes with 0 errors, 0 sorries
- `formNormBall_isRelativelyCompactL2` still compiles (it calls this theorem)
