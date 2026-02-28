/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fourier Symbol Definition and Basic Properties

Reference: lamportform.tex, Section 7.2, lines 783–842 (Lemma 9).

The Fourier symbol ψ_λ(ξ) decomposes the energy form in Fourier space:
  `ψ_λ(ξ) = archFourierSymbol (log λ) ξ + primeFourierSymbol λ ξ`

where:
- archimedean part: `4 ∫_{0}^{2L} w(t) sin²(ξt/2) dt`
- prime part: `4 Σ_p Σ_m (log p) p^{-m/2} sin²(ξ·m·log(p)/2)`

Key properties:
- `ψ_λ(ξ) ≥ 0` (each sin² ≥ 0, all weights positive)
- `ψ_λ(-ξ) = ψ_λ(ξ)` (sin² is even)
- `ψ_λ(0) = 0` (sin(0) = 0)
-/

import ConnesLean.Stage2.ArchimedeanWeight
import ConnesLean.Stage2.PrimeDistribution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fourier Symbol Definition and Basic Properties

Defines the Fourier symbol `ψ_λ(ξ)` decomposing the energy form in Fourier space:
* Archimedean part: `4 ∫₀^{2L} w(t) sin²(ξt/2) dt`
* Prime part: `4 Σ_p Σ_m (log p) p^{-m/2} sin²(ξ · m · log(p) / 2)`

Properties: nonnegativity, evenness (from sin²), and vanishing at zero.

Reference: lamportform.tex, Section 7.2, lines 783–842.
-/

namespace ConnesLean

open MeasureTheory Real Set Finset

noncomputable section

/-! ## Definitions -/

/-- The archimedean part of the Fourier symbol:
    `4 ∫ t in (0, 2L), w(t) sin²(ξt/2) dt`

    Reference: lamportform.tex, line 790. -/
def archFourierSymbol (L ξ : ℝ) : ℝ :=
  4 * ∫ t in Ioo 0 (2 * L), archWeight t * Real.sin (ξ * t / 2) ^ 2 ∂volume

/-- The prime part of the Fourier symbol:
    `4 Σ_{p ∈ primeFinset λ} Σ_{m ∈ exponentFinset p λ} (log p) p^{-m/2} sin²(ξ·m·log(p)/2)`

    Reference: lamportform.tex, line 793. -/
def primeFourierSymbol (cutoffLambda ξ : ℝ) : ℝ :=
  4 * ∑ p ∈ primeFinset cutoffLambda,
    ∑ m ∈ exponentFinset p cutoffLambda,
      Real.log p * (p : ℝ) ^ (-(m : ℝ) / 2) * Real.sin (ξ * ↑m * Real.log ↑p / 2) ^ 2

/-- The full Fourier symbol `ψ_λ(ξ)`, defined as the sum of the archimedean
    and prime parts.

    Reference: lamportform.tex, Lemma 9 (line 797). -/
def fourierSymbol (cutoffLambda ξ : ℝ) : ℝ :=
  archFourierSymbol (Real.log cutoffLambda) ξ + primeFourierSymbol cutoffLambda ξ

/-! ## Nonnegativity -/

/-- The archimedean Fourier symbol is nonneg: each term has `w(t) > 0` and `sin² ≥ 0`. -/
theorem archFourierSymbol_nonneg (L ξ : ℝ) : 0 ≤ archFourierSymbol L ξ := by
  unfold archFourierSymbol
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
  apply setIntegral_nonneg measurableSet_Ioo
  intro t ht
  exact mul_nonneg (le_of_lt (archWeight_pos ht.1)) (sq_nonneg _)

/-- The prime Fourier symbol is nonneg: each term has `log p > 0`, `p^{-m/2} > 0`,
    and `sin² ≥ 0`. -/
theorem primeFourierSymbol_nonneg (cutoffLambda ξ : ℝ) :
    0 ≤ primeFourierSymbol cutoffLambda ξ := by
  unfold primeFourierSymbol
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro m _
  apply mul_nonneg
  · apply mul_nonneg
    · exact le_of_lt (Real.log_pos (Nat.one_lt_cast.mpr
        (Nat.Prime.one_lt (Finset.mem_filter.mp hp).2)))
    · exact le_of_lt (rpow_pos_of_pos (Nat.cast_pos.mpr
        (Nat.Prime.pos (Finset.mem_filter.mp hp).2)) _)
  · exact sq_nonneg _

/-- The full Fourier symbol is nonneg. -/
theorem fourierSymbol_nonneg (cutoffLambda ξ : ℝ) : 0 ≤ fourierSymbol cutoffLambda ξ := by
  unfold fourierSymbol
  exact add_nonneg (archFourierSymbol_nonneg _ _) (primeFourierSymbol_nonneg _ _)

/-! ## Evenness -/

/-- The archimedean Fourier symbol is even: `sin²(-x) = sin²(x)`. -/
theorem archFourierSymbol_even (L ξ : ℝ) :
    archFourierSymbol L (-ξ) = archFourierSymbol L ξ := by
  unfold archFourierSymbol
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  simp only
  congr 1
  rw [show -ξ * t / 2 = -(ξ * t / 2) from by ring, Real.sin_neg, neg_sq]

/-- The prime Fourier symbol is even. -/
theorem primeFourierSymbol_even (cutoffLambda ξ : ℝ) :
    primeFourierSymbol cutoffLambda (-ξ) = primeFourierSymbol cutoffLambda ξ := by
  unfold primeFourierSymbol
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  rw [show -ξ * ↑m * Real.log ↑p / 2 = -(ξ * ↑m * Real.log ↑p / 2) from by ring,
      Real.sin_neg, neg_sq]

/-- The full Fourier symbol is even: `ψ_λ(-ξ) = ψ_λ(ξ)`. -/
theorem fourierSymbol_even (cutoffLambda ξ : ℝ) :
    fourierSymbol cutoffLambda (-ξ) = fourierSymbol cutoffLambda ξ := by
  unfold fourierSymbol
  rw [archFourierSymbol_even, primeFourierSymbol_even]

/-! ## Value at zero -/

/-- The archimedean Fourier symbol vanishes at ξ = 0. -/
theorem archFourierSymbol_zero (L : ℝ) : archFourierSymbol L 0 = 0 := by
  simp [archFourierSymbol, Real.sin_zero]

/-- The prime Fourier symbol vanishes at ξ = 0. -/
theorem primeFourierSymbol_zero (cutoffLambda : ℝ) : primeFourierSymbol cutoffLambda 0 = 0 := by
  simp [primeFourierSymbol, Real.sin_zero]

/-- The full Fourier symbol vanishes at ξ = 0: `ψ_λ(0) = 0`. -/
theorem fourierSymbol_zero (cutoffLambda : ℝ) : fourierSymbol cutoffLambda 0 = 0 := by
  simp [fourierSymbol, archFourierSymbol_zero, primeFourierSymbol_zero]

end

end ConnesLean
