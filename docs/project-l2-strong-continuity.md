# Project: Prove `translation_norm_sq_continuous`

## Goal

Replace the axiom `translation_norm_sq_continuous` in
`ConnesLean/ConnesLean/Stage2/TranslationOperator.lean` with a fully proved
theorem, eliminating one axiom from the formalization.

## Current Axiom

```lean
axiom translation_norm_sq_continuous (φ : ℝ → ℂ) :
    Continuous (fun t => ∫⁻ u, ‖φ u - translationOp t φ u‖₊ ^ (2 : ℝ) ∂volume)
```

This says: for any `φ : ℝ → ℂ`, the map `t ↦ ‖φ − S_t φ‖₂²` is continuous.
Equivalently, the translation group `{S_t}` is strongly continuous on L²(ℝ).

## Mathematical Source

Engel-Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Theorem I.5.8.

Also a standard exercise in Brezis, *Functional Analysis*, Exercise 4.15.

## What Mathlib Already Has (Key Discovery)

Mathlib has **general machinery for strong continuity** of group actions on Lp:

| Mathlib Declaration | File | What it says |
|---|---|---|
| `Lp.instContinuousSMulDomMulAct` | `MeasureTheory/Function/Lp/DomAct/Continuous.lean` | `DomMulAct` action on Lp is continuous |
| `DomMulAct` | `GroupTheory/GroupAction/DomAct/Basic.lean` | Left-regular action of G on functions G → V |
| `measurePreserving_add_left` | `MeasureTheory/Group/LIntegral.lean` | Translation preserves Lebesgue measure |

The `DomMulAct` framework wraps the left-regular action `(g • f)(x) = f(g⁻¹ · x)`.
For `G = ℝ` (additive), this is exactly `S_t φ(u) = φ(u - t)`.

**Alternative approach via density:** Mathlib also has:
- `MeasureTheory.Lp.boundedContinuousFunction_dense` — Cᵦ is dense in Lp
- `MeasureTheory.Lp.simpleFunc_dense` — simple functions dense in Lp
- Uniform continuity of compactly supported functions

## Proof Strategy

### Approach A: Via DomMulAct (Recommended, ~60 lines)

1. **Recognize the action:** Show that `translationOp t φ` is the DomMulAct
   action of `t ∈ ℝ` on `φ`, i.e.:
   ```lean
   translationOp t φ = DomMulAct.mk.symm t • φ
   ```

2. **Apply the continuity instance:** `Lp.instContinuousSMulDomMulAct` gives
   continuity of `t ↦ S_t φ` in the Lp topology (i.e. snorm convergence).

3. **Bridge to concrete norm:** Convert from `snorm` continuity to
   `∫⁻ ‖·‖₊²`-continuity:
   ```lean
   snorm (φ - S_t φ) 2 volume = (∫⁻ u, ‖φ u - S_t φ u‖₊ ^ 2)^(1/2)
   ```
   Continuity of `t ↦ snorm(φ - S_t φ) 2 volume` implies continuity of
   `t ↦ (snorm ...)^2 = ∫⁻ ...`.

**Main challenge:** The DomMulAct framework works with `Lp` quotient types
(equivalence classes of a.e.-equal functions), not with raw functions `ℝ → ℂ`.
Need to bridge between these representations.

### Approach B: Via Density + Uniform Continuity (~100 lines)

Classical proof:

1. **Dense approximation:** For `φ ∈ L²`, approximate by `ψ ∈ C_c(ℝ, ℂ)`
   with `‖φ - ψ‖₂ < ε/3`.

2. **Triangle inequality:**
   ```
   ‖φ - S_t φ‖₂ ≤ ‖φ - ψ‖₂ + ‖ψ - S_t ψ‖₂ + ‖S_t ψ - S_t φ‖₂
                  ≤ ε/3 + ‖ψ - S_t ψ‖₂ + ε/3
   ```
   (using that S_t is an isometry: `‖S_t(ψ - φ)‖₂ = ‖ψ - φ‖₂`).

3. **Continuous case:** For `ψ ∈ C_c`, uniform continuity on the compact support
   gives `‖ψ - S_t ψ‖_∞ → 0` as `t → 0`, hence `‖ψ - S_t ψ‖₂ → 0`.

**Main challenge:** Density of `C_c(ℝ, ℂ)` in `L²(ℝ)` — available in Mathlib
but the API may need careful navigation.

### Approach C: Via Dominated Convergence (~80 lines)

1. For a.e. `u`, `φ(u - t) → φ(u)` as `t → 0` (Lebesgue differentiation).
2. `|φ(u - t) - φ(u)|² ≤ 4|φ(u)|²` (dominating function in L¹ since φ ∈ L²).
3. By dominated convergence, `∫ |φ(u-t) - φ(u)|² du → 0`.

This proves continuity at `t = 0`. Continuity at general `t₀` follows by
replacing `φ` with `S_{t₀} φ`.

**Main challenge:** "For a.e. u, `φ(u - t) → φ(u)` as `t → 0`" is itself
non-trivial for general L² functions. It's true for continuous `φ`, and the
density argument reduces to that case.

## Recommended Approach

**Approach A (DomMulAct)** is recommended because:
- Mathlib already has the hard work done
- The proof is shorter (~60 lines vs ~100)
- It reuses existing, well-tested infrastructure
- It's the most "Mathlib-idiomatic" approach

The main risk is navigating the `DomMulAct` API, which is somewhat abstract.
If this proves too difficult, fall back to Approach B.

## Estimated Effort

| Component | Approach A | Approach B |
|---|---|---|
| Action identification | ~15 lines | — |
| Continuity instantiation | ~10 lines | — |
| Dense approximation | — | ~30 lines |
| Continuous case | — | ~25 lines |
| snorm ↔ lintegral bridge | ~25 lines | ~25 lines |
| Assembly | ~10 lines | ~20 lines |
| **Total** | **~60 lines** | **~100 lines** |

## Dependencies

- **No dependency on other ConnesLean axioms.** This is a standalone
  functional analysis result.
- Depends on Mathlib's `MeasureTheory.Function.Lp.DomAct.Continuous` (Approach A)
  or `MeasureTheory.Lp.boundedContinuousFunction_dense` (Approach B).

## Files to Create/Modify

- **New:** `ConnesLean/ConnesLean/Analysis/TranslationContinuity.lean`
  (self-contained proof)
- **Modify:** `Stage2/TranslationOperator.lean` — change `axiom` to `theorem`,
  import the new file

## Risks and Mitigations

| Risk | Mitigation |
|---|---|
| DomMulAct API is hard to navigate | Fall back to Approach B (density) |
| Lp quotient ↔ raw function bridge is awkward | Mathlib has `Lp.toLp` and `Lp.coeFn`; follow existing patterns |
| `snorm` ↔ `lintegral` conversion is tedious | Same bridge needed for Plancherel project; shared infrastructure |
| Measurability requirements are fiddly | Most follow from `AEStronglyMeasurable` |

## Mathlib Contribution Potential

**Medium.** The result itself is already in Mathlib (via DomMulAct). The
contribution would be in the bridge layer connecting abstract Lp machinery
to concrete integral expressions. Some bridge lemmas (e.g., `snorm_sub_eq_lintegral`)
could be upstreamed.

## Success Criteria

- `translation_norm_sq_continuous` is a `theorem`, not an `axiom`
- `lean_verify` shows no dependency on the old axiom
- `lake build` passes with 0 errors, 0 sorries
- All downstream files (`Stage6/IndicatorEnergy.lean`, etc.) still compile
