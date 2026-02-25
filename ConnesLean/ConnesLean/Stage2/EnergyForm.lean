/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Energy Form E_λ(G) — Definition 3.1

Reference: lamportform.tex, Definition 3.1, lines 435–470.

The difference-energy form assembles the archimedean and prime contributions:
  `E_λ(G) = ∫₀^{2L} w(t) ‖G̃ - S_t G̃‖² dt
           + Σ_p Σ_m (log p) p^{-m/2} ‖G̃ - S_{m log p} G̃‖²`

The total correction constant collects the `‖G‖²` terms from the
energy decompositions:
  `C_λ = Σ_p c_p(λ) + c_∞(λ)`

Key properties:
- `E_λ(G) ≥ 0` (trivially, as ENNReal)
- `c_p(λ) ≤ 0` for each prime p
- `E_λ(0) = 0`
-/

import ConnesLean.Stage2.ArchimedeanDistribution
import ConnesLean.Stage2.PrimeDistribution

namespace ConnesLean

open MeasureTheory Real Finset Set

noncomputable section

/-! ## The energy form -/

/-- The difference-energy form `E_λ(G)` from Definition 3.1 of lamportform.tex.

    For `G : ℝ → ℂ` and cutoff parameter `cutoffLambda > 1` with `L = log cutoffLambda`:
      `E_λ(G) = ∫₀^{2L} w(t) ‖G̃ - S_t G̃‖² dt
              + Σ_{p prime, p ≤ λ²} Σ_{m=1}^{M_p} (log p) p^{-m/2} ‖G̃ - S_{m log p} G̃‖²`

    The first term is the archimedean energy integral; the second is the sum of
    prime energy terms over all relevant primes and exponents.

    Valued in `ENNReal` since each summand is a weighted L² norm (nonneg by construction).

    Reference: lamportform.tex, lines 438–443. -/
def energyForm (cutoffLambda : ℝ) (G : ℝ → ℂ) : ENNReal :=
  let L := Real.log cutoffLambda
  archEnergyIntegral G L +
  ∑ p ∈ primeFinset cutoffLambda, totalPrimeEnergy p cutoffLambda G L

/-! ## The total correction constant -/

/-- The total correction constant `C_λ = Σ_p c_p(λ) + c_∞(λ)`.

    This collects the `‖G‖²` terms from both the prime and archimedean
    energy decompositions. Note that `c_p(λ) ≤ 0` for each prime `p`,
    so the sign of `C_λ` is not controlled in general.

    Reference: lamportform.tex, lines 446–452 (remark after Definition 3.1). -/
def totalCorrection (cutoffLambda : ℝ) : ℝ :=
  (∑ p ∈ primeFinset cutoffLambda, primeConstant p cutoffLambda) +
  archConstant cutoffLambda

/-! ## Basic properties -/

/-- The energy form is nonneg: `E_λ(G) ≥ 0`. Trivial since `ENNReal` is nonneg by definition. -/
theorem energyForm_nonneg (cutoffLambda : ℝ) (G : ℝ → ℂ) :
    (0 : ENNReal) ≤ energyForm cutoffLambda G :=
  zero_le _

/-- Each prime correction term is nonpositive: `c_p(λ) ≤ 0`.
    This follows from `primeConstant_nonpos` together with the fact that
    `primeFinset` membership provides `Nat.Prime p`. -/
theorem totalCorrection_prime_nonpos {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    ∑ p ∈ primeFinset cutoffLambda, primeConstant p cutoffLambda ≤ 0 := by
  apply Finset.sum_nonpos
  intro p hp
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  exact primeConstant_nonpos hprime hLam

/-! ## Zero function gives zero energy -/

/-- Zero-extending the zero function gives the zero function. -/
theorem zeroExtend_zero (I : Set ℝ) : zeroExtend 0 I = 0 := by
  ext u; simp [zeroExtend, Set.indicator_zero']

/-- Translating the zero function gives the zero function. -/
theorem translationOp_apply_zero_fun (t : ℝ) : translationOp t (0 : ℝ → ℂ) = 0 := by
  ext u; simp [translationOp_apply]

/-- The energy form of the zero function is zero: `E_λ(0) = 0`. -/
theorem energyForm_zero (cutoffLambda : ℝ) :
    energyForm cutoffLambda 0 = 0 := by
  unfold energyForm
  suffices h_arch : archEnergyIntegral 0 (Real.log cutoffLambda) = 0 by
    suffices h_prime : ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda 0 (Real.log cutoffLambda) = 0 by
      simp [h_arch, h_prime]
    apply Finset.sum_eq_zero
    intro p _
    unfold totalPrimeEnergy
    apply Finset.sum_eq_zero
    intro m _
    unfold primeEnergyTerm
    simp [zeroExtend_zero]
  unfold archEnergyIntegral archEnergyIntegrand
  simp [zeroExtend_zero]

end

end ConnesLean
