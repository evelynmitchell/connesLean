# Stage 2 Plan: Local Explicit-Formula Terms & Energy Decomposition

## Context

Stage 2 covers Sections 2–3 of `lamportform.tex` (lines 193–470): the local distributions at
primes and at the archimedean place, the logarithmic change of coordinates, and the energy
decomposition into translation differences culminating in Definition `E_λ`.

Blocked by Stage 1 (complete, 0 sorries). Blocks Stage 3 (Markov property, irreducibility).

## Lessons from Stage 1 applied here

1. **Build equivalences early.** `expEquivRPos : ℝ ≃ᵐ RPos` already exists. Stage 2 should
   immediately lift it to an L² isometry, since every downstream proof conjugates through it.

2. **Plain functions first, Lp later.** Define `S_t`, `W_p`, `W_R` as plain functions.
   Prove Lp/integrability properties as separate lemmas, not inline.

3. **The conjugation trick is reusable.** Factor "dilation ↔ translation in log coordinates"
   as a single lemma instead of reproving it per use.

4. **Integrability is the hard part.** Isolate integrability/convergence conditions as
   explicit sorry stubs. These are the last things to close (same pattern as Stage 1).

5. **Finite sums before continuous integrals.** The prime decomposition is algebraic;
   the archimedean decomposition has real singularity analysis. Do them in that order.

6. **Prove integrability before rearrangement.** The LaTeX proof defers convergence
   justification (line 372) but does algebraic manipulation first. In Lean, `integral_add`
   and `integral_sub` require `Integrable` hypotheses upfront. Structure proofs so
   integrability is established before any integral rearrangement.

## File structure

```
ConnesLean/ConnesLean/Stage2/
├── TranslationOperator.lean       # S_t on L²(ℝ) and dilation↔translation correspondence
├── LogCoordinates.lean            # L² isometry exp/log, zero-extension, interval I
├── SupportDisjointness.lean       # Disjoint support → orthogonality, Remark 2 truncation
├── PrimeDistribution.lean         # W_p(f) and lem:prime-energy
├── ArchimedeanWeight.lean         # w(t) definition, sinh bounds, all integrability estimates
├── ArchimedeanDistribution.lean   # W_R(f) definition and lem:arch-energy assembly
└── EnergyForm.lean                # Definition E_λ, assembly from prime + archimedean
```

## Step 1: Translation operator and dilation correspondence

**File:** `TranslationOperator.lean`

**Definitions:**
- `translationOp (t : ℝ) (φ : ℝ → ℂ) : ℝ → ℂ := fun u => φ (u - t)` — plain function
- Simp lemmas: `translationOp_zero`, `translationOp_add` (semigroup law)

**Key theorem (reusable conjugation lemma):**
- `dilation_eq_translation`: For `G(u) = g(exp u)`, `(U_{e^t} g)(exp u) = (S_t G̃)(u)`.
  This factors the conjugation trick used 3+ times in Stage 1 into a single reusable statement.

**Lp properties (separate lemmas):**
- `translationOp_memLp`: `S_t` preserves `MemLp` (measure-preserving via `map_add_left_eq_self`)
- `translationOp_norm_eq`: `‖S_t φ‖₂ = ‖φ‖₂` (L² isometry)

**References:** lamportform.tex lines 244–249.

**Expected sorries:** None — these are elementary.

## Step 2: Logarithmic coordinates and L² isometry

**File:** `LogCoordinates.lean`

**Definitions:**
- `logInterval (λ : ℝ) (hλ : 1 < λ) : Set ℝ := Set.Ioo (-Real.log λ) (Real.log λ)` — the interval I = (-L, L)
- `zeroExtend (G : ℝ → ℂ) (I : Set ℝ) : ℝ → ℂ` — extend by 0 outside I (the G̃ notation).
  Implement as `Set.indicator I G` to leverage Mathlib's `Measurable.indicator`,
  `eLpNorm_indicator_eq_eLpNorm_restrict`, and Lp indicator lemmas.
- `logCoordIso`: The L² isometry lifting `expEquivRPos` to function spaces:
  `L²(R_+*, d*x) ≅ L²(ℝ, du)` via `G(u) = g(exp u)`.

**Key theorem:**
- `norm_dilation_eq_norm_translation`: `‖g - U_a g‖_{L²(d*x)} = ‖G̃ - S_{log a} G̃‖_{L²(du)}`
  This is the content of lem:prime-energy Step 4 and lem:arch-energy Step 5,
  proved once and reused.

**What we reuse from Stage 1:** `expEquivRPos`, `haarMult`, `dilationOp`, `measurable_expToRPos`.

**Expected sorries:** The L² isometry lifting may need careful work with `MeasurePreserving`
and `integral_comp'`. 1–2 sorry stubs for measurability of `zeroExtend`.

## Step 3: Support disjointness and orthogonality

**File:** `SupportDisjointness.lean`

This file collects the support-tracking and orthogonality lemmas used by both the prime
and archimedean decompositions. Corresponds to Remark 2 (rem:truncate, lines 222–233).

**Key lemmas:**
- `support_dilationOp`: `Function.support (dilationOp a g) = (· * a) ⁻¹' Function.support g`
  (i.e., supp(U_a g) = a⁻¹ · supp(g) in multiplicative coordinates)
- `support_translationOp`: `Function.support (translationOp t φ) = (· + t) ⁻¹' Function.support φ`
  (i.e., supp(S_t φ) = t + supp(φ))
- `inner_eq_zero_of_disjoint_support`: If `Function.support u` and `Function.support v` are
  disjoint, then `⟨u, v⟩ = 0`. (Integral of pointwise-zero integrand.)
- `norm_sub_sq_of_disjoint_support`: If supports of φ and ψ are disjoint, then
  `‖φ - ψ‖² = ‖φ‖² + ‖ψ‖²`. (Pythagorean identity from orthogonality.)
- `inner_dilationOp_eq_zero_of_large`: For `supp(g) ⊂ [λ⁻¹, λ]` and `a > λ²`,
  `⟨g, U_a g⟩ = 0`. (Remark 2: supports of g and U_a g are disjoint.)
- `norm_sub_translationOp_of_large`: For `supp(G) ⊂ [-L, L]` and `t > 2L`,
  `‖G̃ - S_t G̃‖² = 2‖G‖²`. (lem:arch-energy Step 6.)

**Interval disjointness (arithmetic):**
- `Icc_disjoint_mul_Icc`: `[λ⁻¹, λ] ∩ [aλ⁻¹, aλ] = ∅` when `a > λ²`.
- `Ioo_disjoint_add_Ioo`: `(-L, L) ∩ (-L + t, L + t) = ∅` when `t > 2L`.

**Expected sorries:** 0–1. These are all elementary measure theory / set arithmetic.

## Step 4: Prime distribution and energy decomposition

**File:** `PrimeDistribution.lean`

**Definitions:**
- `primeDistribution (p : ℕ) (hp : Nat.Prime p) (f : RPos → ℂ) : ℂ` — W_p(f) from eq. (2)
- `primeConstant (p : ℕ) (λ : ℝ) : ℝ` — the constant c_p(λ)

**Finite index set construction (both levels):**
Both the outer sum over primes and the inner sum over exponents need `Finset` construction
from real-valued bounds. Since `ℝ` has no `DecidableEq`, we cannot filter directly.

Workaround — define shared helpers:
- `primeBound (λ : ℝ) : ℕ := Nat.floor (λ^2)` — upper bound for prime index.
  Outer Finset: `Finset.filter Nat.Prime (Finset.range (primeBound λ + 1))`.
  Prove: `(p : ℝ) ≤ λ^2 ↔ p ≤ primeBound λ`.
- `primeExponentBound (p : ℕ) (λ : ℝ) : ℕ := Nat.floor (2 * Real.log λ / Real.log p)` —
  upper bound for exponent index.
  Inner Finset: `Finset.Icc 1 (primeExponentBound p λ)`.
  Prove: `(p : ℝ)^m ≤ λ^2 ↔ m ≤ primeExponentBound p λ` via `Real.log` monotonicity.

These helpers are reused in `EnergyForm.lean` (Step 7) for the same double sum.

**Key theorem (lem:prime-energy):**
```
-W_p(f) = Σ_{m ∈ Finset.Icc 1 N} (log p) p^{-m/2} ‖G̃ - S_{m log p} G̃‖² + c_p(λ) ‖G‖²
```

**Proof strategy:** Entirely algebraic, chaining Stage 1 results:
1. Expand W_p using Lemma 1 part 3: `f(a) + f(a⁻¹) = 2 Re⟨g, U_a g⟩` (already proved)
2. Apply Lemma 2: `2 Re⟨h, Uh⟩ = 2‖h‖² - ‖h - Uh‖²` (already proved)
3. Support truncation from Step 3: `⟨g, U_a g⟩ = 0` for `a > λ²`
4. Change to log coordinates via Step 2's `norm_dilation_eq_norm_translation`
5. Collect the `‖G‖²` terms into `c_p(λ)`

**Expected sorries:** 0–1. The Nat.floor coercion for the index set is the main new work.

## Step 5: Archimedean weight and integrability estimates

**File:** `ArchimedeanWeight.lean`

This is the **hard analytic file**, isolated so the estimates are independently provable
and don't block the algebraic assembly in Step 6.

**Definitions:**
- `archWeight (t : ℝ) : ℝ := exp (t/2) / (2 * Real.sinh t)` — the weight w(t) > 0

**Analytic bounds (the core difficulty):**

| Lemma | Statement | Proof technique |
|-------|-----------|-----------------|
| `sinh_ge_self` | `sinh t ≥ t` for `t ≥ 0` | Integrate `cosh t ≥ 1`; or use Mathlib `Real.self_le_sinh_iff` |
| `archWeight_le_inv_two_t` | `w(t) ≤ e^{t/2} / (2t)` for `t > 0` | Direct from `sinh t ≥ t` |
| `archWeight_pos` | `w(t) > 0` for `t > 0` | From `exp_pos` and `sinh_pos` |
| `abs_exp_neg_half_sub_one_le` | `|e^{-t/2} - 1| ≤ t/2` for `t ≥ 0` | Mean value theorem: `|e^{-x} - 1| ≤ x` for `x ≥ 0` |
| `one_div_sinh_le` | `1/sinh(t) < 4e^{-t}` for `t ≥ 1` | From `e^t - e^{-t} > e^t/2` when `t ≥ 1` |

**Integrability lemmas:**

| Lemma | Statement | Proof technique |
|-------|-----------|-----------------|
| `arch_tail_integrable` | `∫_{2L}^∞ 1/sinh(t) dt < ∞` | Comparison with `4e^{-t}` via `one_div_sinh_le` |
| `arch_correction_integrable` | `∫₀^{2L} \|e^{-t/2} - 1\| w(t) dt < ∞` | Bound by `e^L/2` on compact `[0, 2L]` via `abs_exp_neg_half_sub_one_le` + `archWeight_le_inv_two_t` |
| `archWeight_integrable_on` | `IntegrableOn w (Set.Ioc 0 (2*L))` | Bounded continuous on compact interval (singularity at 0 is removable after cancellation) |

**Measurability of the outer integrand:**
- `measurable_norm_sub_translationOp_sq`: The map `t ↦ ‖G̃ - S_t G̃‖²` is measurable.
  Requires continuity of `t ↦ S_t φ` in L² topology. Mathlib has the ingredients
  (`Continuous.integral`, `MeasurePreserving` for translation) but assembly is nontrivial.
  This is a **prerequisite** for the outer integral to type-check.

**References:** lamportform.tex lines 329–332 (w(t) definition), 399–416 (estimates).

**Expected sorries:** 3–5. The integrability lemmas and measurability of the outer integrand
are the main work. The pointwise bounds should be provable without sorry.

## Step 6: Archimedean distribution and energy assembly

**File:** `ArchimedeanDistribution.lean`

With the weight estimates isolated in Step 5, this file is now mostly algebraic
(same difficulty as PrimeDistribution.lean).

**Definitions:**
- `archDistribution (f : RPos → ℂ) : ℂ` — W_R(f) from eq. (3),
  using `Real.eulerMascheroniConstant` for γ. Mathlib provides this with bounds
  `1/2 < γ < 2/3` and convergence from harmonic series.
- `archConstant (λ : ℝ) : ℝ` — the constant c_∞(λ)

**Key theorem (lem:arch-energy):**
```
-W_R(f) = ∫₀^{2L} w(t) ‖G̃ - S_t G̃‖² dt + c_∞(λ) ‖G‖²
```

**Proof strategy (restructured from LaTeX to satisfy Lean's integrability-first requirement):**

1. **Establish integrability** of all terms (import from ArchimedeanWeight.lean).
   This must come first — Lean's `integral_add`, `integral_sub` need `Integrable` hypotheses.
2. **Change of variables** `x = e^t` in W_R (measure-theoretic, using `expEquivRPos`).
3. **Substitute** Lemma 1 (`f(1) = ‖g‖²`, `f(e^t) + f(e^{-t}) = 2 Re⟨g, U_{e^t} g⟩`)
   and Lemma 2 (`2 Re⟨·,·⟩ = 2‖·‖² - ‖· - ·‖²`).
4. **Split integral** at `t = 2L` (import disjoint support result from Step 3).
5. **Collect** `‖G‖²`-proportional terms into `c_∞(λ)`.
6. **Prove finiteness** of `c_∞(λ)` (sum of three finite quantities from Step 5 estimates).

**References:** lamportform.tex lines 206–219 (W_R definition), 326–430 (lem:arch-energy).

**Expected sorries:** 0–2. The hard work is in ArchimedeanWeight.lean. This file chains results.

## Step 7: Energy form definition

**File:** `EnergyForm.lean`

**Definition (Definition 3.1, line 435):**
```
E_λ(G) := ∫₀^{2L} w(t) ‖G̃ - S_t G̃‖² dt
         + Σ_{p prime, p≤λ²} Σ_{m≥1, p^m≤λ²} (log p) p^{-m/2} ‖G̃ - S_{m log p} G̃‖²
```

**Key theorem (assembly):**
```
-Σ_v W_v(f) = E_λ(G) + C_λ ‖G‖²
```
where `C_λ = Σ_p c_p(λ) + c_∞(λ)` is a finite constant.

**Properties provable in Stage 2:**
- `energyForm_nonneg`: `E_λ(G) ≥ 0` (each term is a squared norm times a positive weight).
  Immediate from `mul_nonneg` + `sq_nonneg` for the prime terms, and
  `integral_nonneg` + `archWeight_pos` for the archimedean term.

**Expected sorries:** 0–1. The assembly is combining Steps 4 and 6.

## Corner cases and risks

### High risk

1. **Archimedean singularity near t = 0.** The weight `w(t) ~ 1/(2t)` as `t → 0`. Formalizing
   the cancellation `O(t) · O(1/t) = O(1)` requires Taylor expansion or L'Hopital-style bounds.
   Mathlib has `Real.sinh` with derivatives and positivity, but the bound `sinh t ≥ t`
   (needed for `archWeight_le_inv_two_t`) must be assembled from `cosh t ≥ 1` + integration.

2. **Absolute convergence ordering.** The LaTeX proof (line 372) defers convergence
   justification but does algebraic rearrangement first. In Lean, `integral_add` and
   `integral_sub` require `Integrable` hypotheses. The proof must be restructured:
   establish all integrability first (Step 5), then rearrange (Step 6).

3. **Measurability of `t ↦ ‖G̃ - S_t G̃‖²`.** This is a prerequisite for the outer integral
   to type-check. Requires proving that `t ↦ S_t φ` is continuous (or at least measurable)
   in the L² topology. Mathlib has the building blocks but no prebuilt lemma.

4. **Finite sums with real-valued bounds (both levels).** Two nested sums need `Finset`
   construction from real bounds:
   - **Outer sum over primes:** `Σ_{p prime, p ≤ λ²}` requires
     `Finset.filter Nat.Prime (Finset.range (Nat.floor (λ^2) + 1))`. This needs
     `Nat.floor` coercion from `ℝ` to `ℕ`, plus proof that `(p : ℝ) ≤ λ^2 ↔ p ≤ ⌊λ²⌋`.
   - **Inner sum over powers:** `Σ_{m ≥ 1, p^m ≤ λ²}` requires
     `Finset.Icc 1 (Nat.floor (2 * Real.log λ / Real.log p))`, plus proof that
     `(p : ℝ)^m ≤ λ^2 ↔ m ≤ N` via `Real.log` monotonicity.
   - Both levels involve the same `Nat.floor` / `Real.log` / `Nat.cast` coercion dance.
     Factor into a shared helper: `primeExponentBound (p : ℕ) (λ : ℝ) : ℕ` and
     `primeBound (λ : ℝ) : ℕ` with the corresponding iff lemmas.
   - The `EnergyForm.lean` definition also has the same double sum, so these helpers
     are used in Steps 4 and 7.

### Medium risk

5. **Zero-extension measurability.** `zeroExtend G I` (implemented as `Set.indicator I G`)
   must be measurable if `G` is. Follows from `Measurable.indicator` in Mathlib, but needs
   `MeasurableSet I` (true for `Set.Ioo`).

6. **Convexity bound `|e^{-t/2} - 1| ≤ t/2`.** Used in arch correction integrability.
   Provable via mean value theorem (`|e^{-x} - 1| ≤ x` for `x ≥ 0` since `|d/dx e^{-x}| ≤ 1`
   on `[0, ∞)`), but needs an explicit lemma.

7. **Euler-Mascheroni constant API.** `W_R(f)` involves `γ`. Mathlib defines
   `Real.eulerMascheroniConstant` with bounds `1/2 < γ < 2/3` and convergence from harmonic
   series. We only need it as a real constant in the definition of `W_R` — no special
   properties required beyond existence.

### Low risk

8. **Inner product convention.** Same as Stage 1 — `Re⟨h, Uh⟩` is convention-independent.
   Document in each file header.

9. **`1/sinh(t) < 4e^{-t}` for `t ≥ 1`.** Elementary: `e^t > 2` and `e^{-t} < 1` for `t ≥ 1`,
   so `sinh t = (e^t - e^{-t})/2 > e^t/4`. Needs only basic exponential inequalities.

## Mathlib availability (verified)

All required constructs exist in Mathlib v4.28.0:

| Construct | Mathlib location | Status |
|-----------|-----------------|--------|
| `Real.sinh` | `Analysis.SpecialFunctions.Trigonometric.DerivHyp` | Full API: derivatives, monotonicity, positivity, bounds |
| `eulerMascheroniConstant` | `NumberTheory.Harmonic.EulerMascheroni` | Bounds: `1/2 < γ < 2/3`, convergence proofs |
| `Set.indicator` for Lp | `MeasureTheory.Function.LpSpace.Indicator` | `eLpNorm_indicator_eq_eLpNorm_restrict` |
| `Nat.Prime` + `Finset.filter` | `Data.Nat.Prime.Defs` + `Data.Finset.Basic` | Decidable primality, standard filtering |
| `MeasurePreserving` for translation | `Dynamics.Ergodic.MeasurePreserving` | Full composition/equivalence machinery |
| `Real.log` on naturals | `Analysis.SpecialFunctions.Log.Basic` | `log_exp`, `exp_log`, monotonicity |
| `intervalIntegral` | `MeasureTheory.Integral.IntervalIntegral.Basic` | `∫ x in a..b, f x` with full API |
| `IntegrableOn` | `MeasureTheory.Integral.IntegrableOn` | Auto for bounded continuous on compact |

## Verification checklist

1. `lake build ConnesLean` compiles without errors
2. `grep -rn sorry ConnesLean/Stage2/` to audit remaining sorries
3. CI sorry regression check passes (added in this PR, between Stages 1 and 2)
4. Each file has a module docstring referencing the corresponding section/lemma in `lamportform.tex`
5. Stage 1 definitions and theorems import cleanly into Stage 2 files
6. Integrability lemmas are proved before any integral rearrangement that depends on them

## Dependency graph

```
Stage 1 (complete)
  ├── expEquivRPos, haarMult, dilationOp
  ├── convolution_eq_inner, convolution_add_inv (Lemma 1)
  └── unitary_identity (Lemma 2)
        │
        ▼
  TranslationOperator.lean ◄──── LogCoordinates.lean
        │                              │
        ▼                              ▼
  SupportDisjointness.lean    ArchimedeanWeight.lean
        │                              │
        ▼                              ▼
  PrimeDistribution.lean      ArchimedeanDistribution.lean
        │                              │
        └──────────┬───────────────────┘
                   ▼
            EnergyForm.lean
```

## Suggested implementation order

1. **TranslationOperator.lean** — no dependencies beyond Stage 1, unblocks everything
2. **LogCoordinates.lean** — depends on TranslationOperator, unblocks both decompositions
3. **SupportDisjointness.lean** — depends on TranslationOperator + LogCoordinates
4. **PrimeDistribution.lean** — algebraic, depends on Steps 1–3, quick win
5. **ArchimedeanWeight.lean** — hard analytic file, can be done in parallel with Step 4
6. **ArchimedeanDistribution.lean** — depends on Steps 1–3 + 5, mostly assembly
7. **EnergyForm.lean** — final assembly, depends on Steps 4 + 6
