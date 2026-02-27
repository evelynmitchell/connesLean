# Project: Plancherel Bridge — Eliminate Stage 5C Axioms

## Goal

Connect Mathlib's existing Plancherel theorem to the concrete integral
identities used in ConnesLean, eliminating up to 4 axioms in Stage 5C
(`ClosedForm.lean`) and unblocking the `formNormBall_equicontinuous` proof.

## Axioms This Would Eliminate

### Primary targets (Stage 5C: `ClosedForm.lean`)

1. **`energyForm_eq_fourierSymbol_integral`** (line 77)
   ```lean
   axiom energyForm_eq_fourierSymbol_integral (cutoffLambda : ℝ)
       (hLam : 1 < cutoffLambda) (G : ℝ → ℂ)
       (hG : G ∈ formDomain cutoffLambda) :
       (energyForm cutoffLambda G).toReal =
       (1 / (2 * Real.pi)) *
       ∫ ξ, fourierSymbol cutoffLambda ξ * ‖FourierTransform.fourier G ξ‖ ^ 2
   ```

2. **`formDomain_eq_weighted_fourier`** (line 93)
   ```lean
   axiom formDomain_eq_weighted_fourier (cutoffLambda : ℝ)
       (hLam : 1 < cutoffLambda) (G : ℝ → ℂ) :
       G ∈ formDomain cutoffLambda ↔
       (∫⁻ ξ, ↑‖FourierTransform.fourier G ξ‖₊ ^ 2 < ⊤ ∧
        ∫⁻ ξ, ↑(fourierSymbol cutoffLambda ξ).toNNReal *
          ↑‖FourierTransform.fourier G ξ‖₊ ^ 2 < ⊤)
   ```

3. **`energyForm_closed_on_line`** (line 116)
   ```lean
   axiom energyForm_closed_on_line (cutoffLambda : ℝ)
       (hLam : 1 < cutoffLambda) : IsClosedEnergyForm cutoffLambda
   ```

4. **`energyForm_closed_on_interval`** (line 133)
   ```lean
   axiom energyForm_closed_on_interval (cutoffLambda : ℝ)
       (hLam : 1 < cutoffLambda) :
       ∀ (Gn : ℕ → ℝ → ℂ) (G : ℝ → ℂ), ...
   ```

### Downstream impact

Proving these would also unblock the proof of `formNormBall_equicontinuous`
(see `docs/project-formNormBall-equicontinuity.md`), which depends on the
Fourier representation.

## What Mathlib Already Has (Key Discovery)

**Mathlib already has the Plancherel theorem.** Specifically:

| Mathlib Declaration | File | What it says |
|---|---|---|
| `MeasureTheory.memℒp_fourierIntegral` | `Analysis/Fourier/LpSpace.lean` | Fourier transform maps L¹ ∩ L² → L² |
| `norm_fourier_eq` | `Analysis/Fourier/LpSpace.lean` | `‖f̂‖₂ = ‖f‖₂` (Plancherel) |
| `inner_fourier_eq` | `Analysis/Fourier/LpSpace.lean` | `⟨f̂, ĝ⟩ = ⟨f, g⟩` (Parseval) |
| `fourierTransformₗᵢ` | `Analysis/Fourier/LpSpace.lean` | Linear isometry `L²(ℝ) →ₗᵢ L²(ℝ)` |

This means **no new Mathlib contribution is needed for Plancherel itself**.
The work is in bridging Mathlib's `L²` formulation (using `Memℒp`, `snorm`,
`Lp` types) to ConnesLean's concrete `∫⁻ u, ‖f u‖₊ ^ 2` formulation.

## Proof Strategy

### Step 1: Translation Difference Identity (~30 lines)

Prove: for `φ ∈ L²(ℝ)` and `t ∈ ℝ`:

```
‖φ − S_t φ‖₂² = (1/2π) ∫ 4 sin²(ξt/2) |φ̂(ξ)|² dξ
```

**Approach:**
- `S_t φ` has Fourier transform `e^{-itξ} φ̂(ξ)` (translation-modulation duality)
- `|e^{-itξ} - 1|² = 4 sin²(tξ/2)` (algebraic identity)
- Apply Plancherel (`norm_fourier_eq`) to get the L² norm identity

**Mathlib tools:** `fourierTransformₗᵢ` for the isometry, `Real.fourierIntegral`
for the concrete transform.

### Step 2: Fourier Representation of Energy Form (~50 lines)

Substitute the translation difference identity into the energy form definition:

```
E_λ(G) = ∫₀^{2L} w(t) ‖G − S_t G‖₂² dt + Σ_p Σ_m (prime terms)
       = (1/2π) ∫ [∫₀^{2L} w(t) 4sin²(ξt/2) dt + Σ_p...] |Ĝ(ξ)|² dξ
       = (1/2π) ∫ ψ_λ(ξ) |Ĝ(ξ)|² dξ
```

**Key challenge:** Fubini interchange — swapping the order of integration
between the spatial/frequency variable ξ and the weight variable t. Need:
- `MeasureTheory.lintegral_lintegral_swap` or `Fubini.lintegral`
- Measurability of the integrand (product of measurable functions)
- Integrability conditions (from the form domain hypothesis)

This proves `energyForm_eq_fourierSymbol_integral`.

### Step 3: Form Domain Characterization (~30 lines)

The form domain condition `E_λ(G) < ∞` becomes, via Step 2:

```
G ∈ D(E_λ) ↔ G ∈ L² ∧ ∫ ψ_λ(ξ) |Ĝ(ξ)|² dξ < ∞
```

The first condition `G ∈ L²` is equivalent (by Plancherel) to `Ĝ ∈ L²`.

This proves `formDomain_eq_weighted_fourier`.

### Step 4: Closedness (~40 lines)

For `energyForm_closed_on_line` (`IsClosedEnergyForm`):
- **Nonneg:** Trivial (ENNReal).
- **Zero energy:** From existing `energyForm_zero`.
- **Smooth in domain:** For `φ ∈ C_c^∞`, use MVT: `‖φ − S_t φ‖ ≤ |t| · ‖φ'‖`.
  The energy integral converges because `w(t) · t²` is integrable on `(0, 2L)`.
- **Graph completeness:** The graph norm equals `(1/2π) ∫ (1 + ψ_λ(ξ)) |Ĝ(ξ)|² dξ`.
  This is a weighted L² norm; weighted L² is complete (closed subspace of L²).

For `energyForm_closed_on_interval`: combine closedness on ℝ with the fact
that `H_I = {φ : supp(φ) ⊆ I}` is a closed subspace of L².

## Bridge Layer: Concrete ↔ Abstract L²

The main technical work is building a bridge between:
- **ConnesLean's style:** `∫⁻ u, ‖f u‖₊ ^ (2 : ℝ)` (raw Lebesgue integrals)
- **Mathlib's style:** `snorm f 2 μ`, `Memℒp f 2 μ`, `Lp` quotient types

Key bridge lemmas needed (~40 lines):

```lean
-- Bridge: raw integral = snorm squared
theorem lintegral_nnnorm_sq_eq_snorm_sq (f : ℝ → ℂ) (hf : Memℒp f 2 volume) :
    ∫⁻ u, ‖f u‖₊ ^ (2 : ℝ) = snorm f 2 volume ^ 2

-- Bridge: Fourier of translation difference
theorem fourier_translationOp (t : ℝ) (φ : ℝ → ℂ) (ξ : ℝ) :
    FourierTransform.fourier (translationOp t φ) ξ =
    Complex.exp (-2 * Real.pi * Complex.I * t * ξ) * FourierTransform.fourier φ ξ
```

## Estimated Effort

| Component | Lines | Difficulty |
|---|---|---|
| Bridge layer (snorm ↔ lintegral) | ~40 | Medium |
| Fourier of translation | ~20 | Easy |
| Translation difference identity | ~30 | Medium |
| Fourier representation (+ Fubini) | ~50 | Hard |
| Form domain characterization | ~30 | Medium |
| Closedness (line + interval) | ~40 | Hard |
| **Total** | **~210** | |

## Dependency Graph

```
Mathlib Plancherel (norm_fourier_eq)
         │
         ▼
Bridge layer (snorm ↔ lintegral)
         │
         ▼
Translation difference identity
         │
    ┌────┴────┐
    ▼         ▼
Fourier    Form domain
rep (1)    char (2)
    │         │
    └────┬────┘
         ▼
Closedness (3, 4)
         │
         ▼
formNormBall_equicontinuous (5D axiom)
```

## Files to Create/Modify

- **New:** `ConnesLean/ConnesLean/Analysis/PlancherelBridge.lean` — bridge lemmas
- **New:** `ConnesLean/ConnesLean/Analysis/FourierTranslation.lean` — Fourier of S_t
- **Modify:** `Stage5/ClosedForm.lean` — replace 4 axioms with theorems
- **Modify:** `Stage5/CompactEmbedding.lean` — proof of equicontinuity becomes reachable

## Risks and Mitigations

| Risk | Mitigation |
|---|---|
| snorm ↔ lintegral bridge is tedious | Pattern exists in Mathlib; search for `snorm_eq_lintegral` |
| Fubini interchange needs careful integrability | The form domain hypothesis provides the needed bounds |
| Fourier transform of translation may need measurability | Use `AEStronglyMeasurable` from Mathlib |
| Closedness proof is multi-part | Can axiomatize MVT estimate as intermediate if needed |

## Mathlib Contribution Potential

**High.** The bridge lemmas (Fourier of translation, translation difference identity
in terms of `snorm`) are general-purpose and would be welcome in Mathlib's
`Analysis/Fourier/` directory. The translation-modulation duality identity in
particular is a fundamental Fourier analysis result.

## Success Criteria

- All 4 axioms in `ClosedForm.lean` replaced by theorems
- `lean_verify` shows no dependency on the old axioms
- `lake build` passes with 0 errors, 0 sorries
- All downstream files (`CompactEmbedding.lean`, `CompactResolvent.lean`) still compile
