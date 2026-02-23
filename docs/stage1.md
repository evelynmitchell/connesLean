# Stage 1 Plan: Multiplicative Hilbert Space Setup

## Context

This is the first stage of formalizing Christopher Long's proof of the Restricted Weil Quadratic Form in Lean4. Stage 1 covers Section 1 of `lamportform.tex` (lines 94–191): the foundational setup on R_+* = (0,∞), including the multiplicative Haar measure, dilation operators, and two key lemmas. This stage has no upstream dependencies and blocks Stages 2–3.

Per the workflow in README.md, this first pass may use `axiom` and `sorry` where needed, with later passes filling them in.

## Step 1: Initialize the Lean4 project with Mathlib dependency

Create the Lean4 project structure:

```
ConnesLean/
├── lakefile.toml
├── lean-toolchain
├── ConnesLean.lean              # Root import file
├── ConnesLean/
│   ├── Stage1/
│   │   ├── MultiplicativeHaar.lean
│   │   ├── DilationOperator.lean
│   │   ├── Convolution.lean
│   │   ├── ConvolutionInnerProduct.lean   # Lemma 1
│   │   └── UnitaryIdentity.lean           # Lemma 2
│   └── Common/
│       └── Notation.lean
└── test/
    └── Stage1Tests.lean
```

Run:
```bash
lake +leanprover/lean4:v4.28.0 new ConnesLean math
cd ConnesLean
lake update
lake exe cache get
```

This gives us Mathlib as a dependency out of the box.

## Step 2: Define the multiplicative Haar measure on (0,∞)

**File:** `ConnesLean/Stage1/MultiplicativeHaar.lean`

**Approach:** Use the exponential map as a measurable isomorphism between (R, +, Lebesgue) and (R_+*, ×, d*x). Define the multiplicative Haar measure as the pushforward of Lebesgue measure under `exp`:

```
μ_mult = Measure.map exp volume
```

This automatically gives `d*x = dx/x` because the Jacobian of exp is `exp`, so `∫ f(x) d(map exp vol) = ∫ f(eᵘ) du`.

**Key Mathlib imports:**
- `Mathlib.MeasureTheory.Measure.Haar`
- `Mathlib.MeasureTheory.Constructions.Prod.Basic` (for map)
- `Mathlib.Analysis.SpecialFunctions.Log.Basic`

**Definitions to provide:**
- `RPos` — the type `{x : ℝ // 0 < x}` (or use `Set.Ioi (0 : ℝ)`)
- `haarMult` — the multiplicative Haar measure on R_+*
- Proof that `haarMult` is left-invariant under multiplication: `haarMult (a • S) = haarMult S`

**First-pass sorrys expected:** The left-invariance proof may use `sorry` initially if the pushforward calculation is complex.

## Step 3: Define the dilation operator and prove unitarity

**File:** `ConnesLean/Stage1/DilationOperator.lean`

**Definitions:**
- `dilationOp (a : ℝ) (ha : 0 < a) : Lp ℂ 2 haarMult → Lp ℂ 2 haarMult` defined by `(U_a g)(x) = g(x/a)`

**Theorems to prove:**
1. `dilationOp_isometry`: `‖U_a g‖ = ‖g‖` — follows from Haar measure invariance under multiplication by `a`
2. `dilationOp_surjective`: `U_a` is surjective with inverse `U_{a⁻¹}`
3. `dilationOp_unitary`: combining the above, `U_a` is a `LinearIsometryEquiv`
4. `inner_dilationOp_bound`: `|⟨g, U_a g⟩| ≤ ‖g‖²` — Cauchy–Schwarz + isometry

**Key Mathlib imports:**
- `Mathlib.MeasureTheory.Function.L2Space`
- `Mathlib.Analysis.InnerProductSpace.Basic`

## Step 4: Define multiplicative convolution and involution

**File:** `ConnesLean/Stage1/Convolution.lean`

**Definitions:**
- `mulConv (g h : Lp ℂ 2 haarMult) : R_+* → ℂ` defined by `(g * h)(x) = ∫ g(y) h(x/y) d*y`
- `mulInvol (g : Lp ℂ 2 haarMult) : Lp ℂ 2 haarMult` defined by `g*(x) = conj(g(x⁻¹))`

**Properties to prove:**
- `mulInvol_apply`: `g*(x) = conj(g(x⁻¹))` (definitional)
- `mulInvol_involutive`: `(g*)* = g`
- `mulConv_mulInvol_eval`: `(g * g*)(a) = ∫ g(y) conj(g(y/a)) d*y`

**Mathlib imports:**
- `Mathlib.MeasureTheory.Group.Convolution` — may provide some scaffolding but the multiplicative version on R_+* likely needs custom definitions

**First-pass sorrys expected:** Measurability of the convolution integrand; integrability conditions.

## Step 5: Formalize Lemma 1 (Convolution inner-product identity)

**File:** `ConnesLean/Stage1/ConvolutionInnerProduct.lean`

**Statement (lamportform.tex Lemma `lem:f-inner`, lines 122–163):**

For `f = g * g*` and `a > 0`:
1. `f(a) = ⟨g, U_a g⟩_{L²(d*x)}`
2. `f(a⁻¹) = conj(f(a))`
3. `f(a) + f(a⁻¹) = 2 Re⟨g, U_a g⟩`
4. `f(1) = ‖g‖²`

**Proof structure:**
- Part 1: Unfold convolution definition, apply involution, recognize as inner product with dilation (Steps 1.1–1.4 in the LaTeX)
- Part 2: Substitute `a⁻¹`, use Haar invariance for the change of variables `y' = ya` (Step 2)
- Part 3: Algebraic consequence of parts 1–2 (Step 3)
- Part 4: Specialization at `a = 1` where `U_1 = id` (Step 3)

**Dependencies:** Steps 2, 3, 4 above.

## Step 6: Formalize Lemma 2 (Basic unitary identity)

**File:** `ConnesLean/Stage1/UnitaryIdentity.lean`

**Statement (lamportform.tex Lemma `lem:unitary`, lines 166–191):**

For any unitary operator `U` on a Hilbert space and any vector `h`:
```
2 Re⟨h, Uh⟩ = 2‖h‖² - ‖h - Uh‖²
```

**Proof structure (4 steps, all elementary algebra):**
1. Expand `‖h - Uh‖² = ‖h‖² + ‖Uh‖² - 2 Re⟨h, Uh⟩` — inner product expansion
2. `‖Uh‖² = ‖h‖²` — unitarity / isometry
3. Substitute: `‖h - Uh‖² = 2‖h‖² - 2 Re⟨h, Uh⟩`
4. Rearrange

**Note:** This lemma is stated for an abstract Hilbert space and unitary operator — it does not depend on the multiplicative setup. It should be stated generically using Mathlib's `InnerProductSpace` and isometry properties.

**Key Mathlib imports:**
- `Mathlib.Analysis.InnerProductSpace.Basic` — `inner_sub_left`, `inner_sub_right`, `norm_sq_eq_inner`
- The proof may reduce to `ring` or `linarith` after unfolding norms into inner products.

**First-pass sorrys expected:** None — this should be fully provable with Mathlib's inner product lemmas.

## Step 7: Write LSpec property tests

**File:** `test/Stage1Tests.lean`

Tests to write:
- `haarMult` is defined and nonzero
- `dilationOp` preserves L² norm (check on a concrete function)
- `dilationOp` inverse is `dilationOp` with `a⁻¹`
- `mulInvol` is involutive
- Unitary identity holds for the identity operator (trivial case: `2 Re⟨h, h⟩ = 2‖h‖² - 0`)

## Step 8: Update root import file

**File:** `ConnesLean.lean`

Add imports for all Stage 1 files so `lake build` compiles the full stage.

## Corner Cases and Risks

### High risk

1. **Representing R_+* = (0,∞) as a type.** Use `{x : ℝ // 0 < x}` (subtype). Alternatives like `Set.Ioi 0`, `ℝ≥0`, or bare `ℝ` with side conditions have worse Mathlib integration for `Lp` spaces and measure theory. The subtype can be equipped with a `MeasureSpace` instance via `Measure.comap Subtype.val`.

2. **`exp` is not a `MeasurableEquiv ℝ ℝ`** (it's not surjective). We need to construct a `MeasurableEquiv ℝ {x : ℝ // 0 < x}` using exp/log explicitly, proving measurability of both directions. This is foundational plumbing that must be done before the pushforward measure.

3. **Sigma-finiteness of pushforward measure.** Mathlib has no explicit theorem that `Measure.map f μ` preserves sigma-finiteness. We must prove this from first principles for the exp pushforward. (Mathematically straightforward but may require manual construction of a countable cover.)

4. **Convolution pointwise evaluation vs. a.e. equivalence classes.** The paper evaluates `f(a) = (g * g*)(a)` pointwise, but Mathlib's `Lp` uses `AEEqFun` quotient classes. Two options:
   - Work with representatives and carry measurability/integrability proofs
   - Define convolution as a function `R_+* → ℂ` (not an L² element) and prove separately that it agrees with the inner product a.e.

   **Decision:** Define `mulConv` as a plain function `{x : ℝ // 0 < x} → ℂ` (not an Lp element), sidestepping the quotient issue for pointwise evaluation. This matches the paper's usage.

5. **Convolution integrability.** For `g ∈ L²`, the integrand `y ↦ g(y) · conj(g(y/a))` is integrable by Cauchy-Schwarz (both factors are L², and the measure is Haar-invariant). But formalizing this requires:
   - Measurability of the composed function
   - The Cauchy-Schwarz inequality for integrals (available in Mathlib as `inner_mul_le_norm_mul_sq` or via Hölder)
   - Haar invariance to show `y ↦ g(y/a)` is still in L²

   **First pass:** Use `sorry` for integrability; fill in on second pass.

### Medium risk

6. **IsHaarMeasure verification.** Proving the pushforward measure satisfies Mathlib's `IsHaarMeasure` class requires formalizing the multiplicative group structure on `{x : ℝ // 0 < x}` and verifying: left-invariance, finite on compacts, positive on opens. **First pass:** Define the measure directly and prove left-invariance; defer `IsHaarMeasure` instance to second pass.

7. **Dilation operator well-definedness on Lp.** The map `x ↦ x/a` is measurable (continuous, hence measurable) and measure-preserving (by Haar invariance). But to define `U_a` on `Lp` equivalence classes, we need `MeasurePreserving` for the induced map on the subtype. This follows from left-invariance but requires explicit verification.

### Low risk

8. **Inner product convention.** Mathlib uses conjugate-linear-in-first-argument: `inner x y = conj(x) * y`. The paper uses `⟨g,h⟩ = ∫ g(y) conj(h(y)) d*y`, which is conjugate-linear-in-second. **Mitigation:** These differ by complex conjugation of the whole inner product. For real-valued `Re⟨h, Uh⟩`, the convention doesn't matter since `Re(z) = Re(conj(z))`. However, Lemma 1 part 2 (`f(a⁻¹) = conj(f(a))`) needs careful convention tracking. Document the convention mismatch at the top of each file.

9. **Complex-valued L² functions.** Mathlib's `Lp ℂ 2 μ` is well-supported with `InnerProductSpace` structure. No issues expected.

## Verification

1. `lake build` compiles without errors (sorrys are warnings, not errors)
2. `lake test` runs LSpec tests
3. `grep -r sorry ConnesLean/Stage1/` to audit remaining sorrys
4. Each `.lean` file has a module docstring referencing the corresponding section/lemma in `lamportform.tex`
