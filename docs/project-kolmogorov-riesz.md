# Project: Prove `kolmogorov_riesz_compact`

## Goal

Replace the axiom `kolmogorov_riesz_compact` in
`ConnesLean/ConnesLean/Stage5/CompactEmbedding.lean` (line 58) with a
fully proved theorem, eliminating one axiom from the formalization.

## Current Axiom

```lean
axiom kolmogorov_riesz_compact (K : Set (ℝ → ℂ)) (R : ℝ)
    (h_supp : ∀ φ ∈ K, Function.support φ ⊆ Icc (-R) R)
    (h_bdd : ∃ M : ENNReal, M < ⊤ ∧ ∀ φ ∈ K, (∫⁻ u, ‖φ u‖₊ ^ (2 : ℝ)) ≤ M)
    (h_equi : ∀ ε : ENNReal, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ φ ∈ K, ∀ h : ℝ,
      |h| < δ → (∫⁻ u, ‖φ (u - h) - φ u‖₊ ^ (2 : ℝ)) < ε) :
    IsRelativelyCompactL2 K
```

The target type `IsRelativelyCompactL2 K` means: every sequence in K
has a subsequence converging in L² norm to some limit function.

## Mathematical Source

Brezis, *Functional Analysis, Sobolev Spaces and PDEs* (Springer 2011):
- **Theorem 4.26** (bounded domain): Kolmogorov-Riesz for L^p(Ω), Ω bounded.
- **Corollary 4.27** (full line): extends to L^p(ℝ) by adding a tightness
  condition. Our compact-support hypothesis (`h_supp`) is strictly stronger
  than tightness, so it subsumes condition (i).

Also referenced in `lamportform.tex`, lines 1061–1069 (Theorem KR).

## Proof Outline

The proof has two main layers:

### Layer 1: Arzelà-Ascoli on Mollifications

1. **Mollify**: Convolve each φ ∈ K with a standard mollifier ρ_δ to get
   smooth approximations φ_δ = φ * ρ_δ.

2. **Uniform convergence of mollifications on compacta**: The equicontinuity
   hypothesis (`h_equi`) gives ‖φ_δ − φ‖₂ → 0 uniformly over K as δ → 0.
   This is the key step that converts L²-translation-equicontinuity into
   actual proximity in L² norm.

3. **Pointwise equicontinuity of φ_δ**: For fixed δ, the family
   {φ_δ : φ ∈ K} is pointwise equicontinuous and uniformly bounded
   on [−R−1, R+1]. This follows from the L² bound (`h_bdd`) and
   Cauchy-Schwarz applied to the convolution.

4. **Arzelà-Ascoli**: Extract a subsequence along which φ_δ converges
   uniformly on [−R−1, R+1], hence in L².

### Layer 2: Diagonal Extraction

5. **Diagonal argument**: Take δ_k = 1/k. For each k, extract a
   subsequence converging in L². Diagonalize to get a single subsequence
   σ such that φ(σ(n)) is Cauchy in L².

6. **Completeness**: L² is complete (this IS in Mathlib), so the Cauchy
   subsequence converges to some f ∈ L².

## What Mathlib Provides

| Component | Mathlib Status | Reference |
|-----------|---------------|-----------|
| L² completeness | ✅ Available | `MeasureTheory.Lp.instCompleteSpace` |
| Arzelà-Ascoli (topological) | ✅ Available | `ArzelaAscoli` in `Mathlib.Topology.ContinuousMap.Compact` |
| Convolution `f * g` | ✅ Available | `MeasureTheory.Convolution` |
| Mollifier construction | ⚠️ Partial | `ContDiff.hasCompactSupport` tools exist but no standard `ρ_δ` |
| `StrictMono` for subsequences | ✅ Available | `StrictMono`, `Nat.lt_of_lt_pred` etc. |
| Diagonal extraction | ❌ Not available | Need to build or inline |
| L²-norm of convolution bound | ⚠️ Partial | Young's inequality not fully specialized |

## What Needs to Be Built

### A. Mollifier Infrastructure (~40 lines)
- Standard mollifier `ρ_δ : ℝ → ℝ` with `ρ_δ ≥ 0`, `∫ ρ_δ = 1`,
  `support ρ_δ ⊆ [−δ, δ]`
- Can use `ContDiff.hasCompactSupport` building blocks from Mathlib
- Or define directly via bump functions

### B. Mollification Approximation (~30 lines)
- `‖φ * ρ_δ − φ‖₂² ≤ sup_{|h|<δ} ‖τ_h φ − φ‖₂²`
- Follows from Jensen's inequality for the convolution integral
- The equicontinuity hypothesis then gives uniform δ → 0 convergence

### C. Equicontinuity of Mollifications (~25 lines)
- For fixed δ: `|φ_δ(x) − φ_δ(y)| ≤ ‖ρ_δ‖_∞ · ‖τ_{x−y} φ − φ‖₁`
- Combined with L² bound gives `≤ C(δ, M) · |x − y|^{1/2}`
- Uniform bound: `|φ_δ(x)| ≤ ‖ρ_δ‖₂ · M^{1/2}` by Cauchy-Schwarz

### D. Diagonal Subsequence Extraction (~30 lines)
- Given a sequence of subsequence extractions, produce a single
  diagonal subsequence
- Pure combinatorics, no analysis needed
- Could be a reusable utility

### E. Assembly (~20 lines)
- Combine A–D into the final proof
- For each k: use equicontinuity + Arzelà-Ascoli to extract subsequence
- Diagonalize, verify L² Cauchy, invoke completeness

## Estimated Effort

~150–200 lines of Lean code total. The proof is elementary (no deep
theorems beyond Arzelà-Ascoli and L² completeness) but requires
careful bookkeeping of the ε-δ arguments and subsequence management.

## Dependencies

- **None on other axioms in this project.** KR is a standalone
  functional analysis result.
- Depends on Mathlib's measure theory and convolution libraries.
- Does NOT require Plancherel, Fourier transforms, or any spectral theory.

## Files to Create/Modify

- **New file**: `ConnesLean/ConnesLean/Stage5/KolmogorovRiesz.lean`
  (self-contained proof of the theorem)
- **Modify**: `CompactEmbedding.lean` — change `axiom` to `theorem`,
  importing the new file
- **Modify**: Tests to verify the axiom is gone

## Risks and Mitigations

| Risk | Mitigation |
|------|-----------|
| Mollifier construction is fiddly in Lean | Can axiomatize just the mollifier properties and prove the rest |
| Arzelà-Ascoli API may not match our needs | The topological version exists; may need a specialization for `ℝ → ℂ` on bounded intervals |
| Diagonal extraction is tedious | Standard pattern; consider a general `diag_subseq` utility |
| Young's inequality gap | Can prove the specific L²×L¹ → L² case directly via Cauchy-Schwarz |

## Success Criteria

- `kolmogorov_riesz_compact` is a `theorem`, not an `axiom`
- `lean_verify` shows it depends only on standard Lean axioms
  (propext, Classical.choice, Quot.sound) — no custom axioms
- `lake build` passes with 0 errors, 0 sorries
- All downstream theorems (`formNormBall_isRelativelyCompactL2`) still compile
