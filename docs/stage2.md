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

## File structure

```
ConnesLean/ConnesLean/Stage2/
├── TranslationOperator.lean       # S_t on L²(ℝ) and dilation↔translation correspondence
├── LogCoordinates.lean            # L² isometry exp/log, zero-extension, interval I
├── PrimeDistribution.lean         # W_p(f) and lem:prime-energy
├── ArchimedeanDistribution.lean   # W_R(f), weight w(t), and lem:arch-energy
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
- `zeroExtend (G : ℝ → ℂ) (I : Set ℝ) : ℝ → ℂ` — extend by 0 outside I (the G̃ notation)
- `logCoordIso`: The L² isometry lifting `expEquivRPos` to function spaces:
  `L²(R_+*, d*x) ≅ L²(ℝ, du)` via `G(u) = g(exp u)`.

**Key theorem:**
- `norm_dilation_eq_norm_translation`: `‖g - U_a g‖_{L²(d*x)} = ‖G̃ - S_{log a} G̃‖_{L²(du)}`
  This is the content of lem:prime-energy Step 4 and lem:arch-energy Step 5,
  proved once and reused.

**What we reuse from Stage 1:** `expEquivRPos`, `haarMult`, `dilationOp`, `measurable_expToRPos`.

**Expected sorries:** The L² isometry lifting may need careful work with `MeasurePreserving`
and `integral_comp'`. 1–2 sorry stubs for measurability of `zeroExtend`.

## Step 3: Prime distribution and energy decomposition

**File:** `PrimeDistribution.lean`

**Definitions:**
- `primeDistribution (p : ℕ) (hp : Nat.Prime p) (f : RPos → ℂ) : ℂ` — W_p(f) from eq. (2)
- `primeConstant (p : ℕ) (λ : ℝ) : ℝ` — the constant c_p(λ)

**Key theorem (lem:prime-energy):**
```
-W_p(f) = Σ_{m≥1, p^m≤λ²} (log p) p^{-m/2} ‖G̃ - S_{m log p} G̃‖² + c_p(λ) ‖G‖²
```

**Proof strategy:** This is entirely algebraic, chaining Stage 1 results:
1. Expand W_p using Lemma 1 part 3: `f(a) + f(a⁻¹) = 2 Re⟨g, U_a g⟩` (already proved)
2. Apply Lemma 2: `2 Re⟨h, Uh⟩ = 2‖h‖² - ‖h - Uh‖²` (already proved)
3. Support truncation: `⟨g, U_a g⟩ = 0` for `a > λ²` (disjoint supports — new, but easy)
4. Change to log coordinates via Step 2's `norm_dilation_eq_norm_translation`
5. Collect the `‖G‖²` terms into `c_p(λ)`

**The sum is finite** (only finitely many m with p^m ≤ λ²), so no convergence issues.

**Expected sorries:** 0–1. The support disjointness lemma (Remark 2) is the only new content;
everything else chains existing results.

## Step 4: Archimedean distribution and energy decomposition

**File:** `ArchimedeanDistribution.lean`

**Definitions:**
- `archWeight (t : ℝ) : ℝ := exp (t/2) / (2 * Real.sinh t)` — the weight w(t)
- `archDistribution (f : RPos → ℂ) : ℂ` — W_R(f) from eq. (3)
- `archConstant (λ : ℝ) : ℝ` — the constant c_∞(λ)

**Key theorem (lem:arch-energy):**
```
-W_R(f) = ∫₀^{2L} w(t) ‖G̃ - S_t G̃‖² dt + c_∞(λ) ‖G‖²
```

**This is the hard file.** The proof requires:

1. Change of variables `x = e^t` in the W_R integral (lines 343–353)
2. Substitution using Lemma 1 and Lemma 2 (same algebraic chain as primes)
3. **Singularity analysis near t = 0**: the integrand has a `1/t` singularity from `w(t) ~ 1/(2t)`,
   cancelled by `f(e^t) + f(e^{-t}) - 2e^{-t/2}f(1) = O(t)` (Taylor expansion, line 350–351)
4. **Tail estimate**: `∫_{2L}^∞ 1/sinh(t) dt < ∞` (exponential decay, lines 399–403)
5. **Disjoint supports for t > 2L**: `‖G̃ - S_t G̃‖² = 2‖G‖²` (same as Remark 2)
6. Finiteness of `c_∞(λ)` (collect all `‖G‖²`-proportional terms)

**Integrability lemmas (separate, with sorry stubs):**
- `archWeight_integrable_on`: `w` is integrable on `[0, 2L]` (singularity at 0 is integrable)
- `arch_tail_integrable`: `∫_{2L}^∞ 1/sinh(t) dt < ∞`
- `arch_correction_integrable`: `∫₀^{2L} |e^{-t/2} - 1| w(t) dt < ∞`

**Expected sorries:** 3–5. The integrability/convergence lemmas are the main work.
The algebraic assembly is similar to the prime case.

## Step 5: Energy form definition

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

**Properties to state (proved later in Stage 3, stated here as sorry stubs for forward reference):**
- `energyForm_nonneg`: `E_λ(G) ≥ 0` (each term is a squared norm times a positive weight)
- Nonnegativity is *immediate* from the definition — this should be provable in Stage 2.

**Expected sorries:** 0–1. The assembly is combining Steps 3 and 4.
Nonnegativity is a one-liner from `mul_nonneg` + `sq_nonneg`.

## Corner cases and risks

### High risk

1. **Archimedean singularity near t = 0.** The weight `w(t) ~ 1/(2t)` as `t → 0`. Formalizing
   the cancellation `O(t) · O(1/t) = O(1)` requires Taylor expansion or L'Hôpital-style bounds.
   Mathlib has `Real.sinh` and basic asymptotics but may not have the exact bound we need.

2. **Finite sums over primes.** The sum `Σ_{p prime, p≤λ²}` requires a `Finset` of primes
   bounded by `λ²`. Mathlib has `Nat.Prime` and `Finset.filter`, but the interaction with
   real-valued `λ` (converting `p ≤ λ²` to a decidable `Nat` bound) needs care.

3. **Euler-Mascheroni constant.** `W_R(f)` involves `γ`. Mathlib defines `Real.eulerMascheroniConstant`.
   Check that it has the properties we need (it may be defined but have few lemmas).

### Medium risk

4. **Zero-extension measurability.** `zeroExtend G I` must be measurable if `G` is.
   Should follow from `Set.indicator` measurability, but needs explicit verification.

5. **The norm-squared function `t ↦ ‖G̃ - S_t G̃‖²` must be measurable as a function of t**
   for the outer integral to make sense. This requires continuity or measurability of
   the map `t ↦ S_t φ` in the L² topology.

### Low risk

6. **Inner product convention.** Same as Stage 1 — `Re⟨h, Uh⟩` is convention-independent.
   Document in each file header.

## Verification checklist

1. `lake build ConnesLean` compiles without errors
2. `grep -rn sorry ConnesLean/Stage2/` to audit remaining sorries
3. CI sorry regression check passes (added in Stage 1)
4. Each file has a module docstring referencing the corresponding section/lemma in `lamportform.tex`
5. Stage 1 definitions and theorems import cleanly into Stage 2 files

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
  PrimeDistribution.lean      ArchimedeanDistribution.lean
        │                              │
        └──────────┬───────────────────┘
                   ▼
            EnergyForm.lean
```
