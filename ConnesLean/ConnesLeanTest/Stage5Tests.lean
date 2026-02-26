/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 5 Property Tests

Verification tests for Stage 5 definitions and theorems covering
the Fourier symbol and its basic properties.
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real

noncomputable section

/-! ## archFourierSymbol tests -/

/-- The archimedean Fourier symbol is nonneg. -/
example (L ξ : ℝ) : 0 ≤ archFourierSymbol L ξ :=
  archFourierSymbol_nonneg L ξ

/-- The archimedean Fourier symbol is even. -/
example (L ξ : ℝ) : archFourierSymbol L (-ξ) = archFourierSymbol L ξ :=
  archFourierSymbol_even L ξ

/-- The archimedean Fourier symbol vanishes at zero. -/
example (L : ℝ) : archFourierSymbol L 0 = 0 :=
  archFourierSymbol_zero L

/-! ## primeFourierSymbol tests -/

/-- The prime Fourier symbol is nonneg. -/
example (cutoffLambda ξ : ℝ) : 0 ≤ primeFourierSymbol cutoffLambda ξ :=
  primeFourierSymbol_nonneg cutoffLambda ξ

/-- The prime Fourier symbol is even. -/
example (cutoffLambda ξ : ℝ) :
    primeFourierSymbol cutoffLambda (-ξ) = primeFourierSymbol cutoffLambda ξ :=
  primeFourierSymbol_even cutoffLambda ξ

/-- The prime Fourier symbol vanishes at zero. -/
example (cutoffLambda : ℝ) : primeFourierSymbol cutoffLambda 0 = 0 :=
  primeFourierSymbol_zero cutoffLambda

/-! ## fourierSymbol tests -/

/-- The full Fourier symbol is nonneg. -/
example (cutoffLambda ξ : ℝ) : 0 ≤ fourierSymbol cutoffLambda ξ :=
  fourierSymbol_nonneg cutoffLambda ξ

/-- The full Fourier symbol is even. -/
example (cutoffLambda ξ : ℝ) :
    fourierSymbol cutoffLambda (-ξ) = fourierSymbol cutoffLambda ξ :=
  fourierSymbol_even cutoffLambda ξ

/-- The full Fourier symbol vanishes at zero. -/
example (cutoffLambda : ℝ) : fourierSymbol cutoffLambda 0 = 0 :=
  fourierSymbol_zero cutoffLambda

/-! ## Decomposition test -/

/-- The Fourier symbol decomposes into arch + prime parts. -/
example (cutoffLambda ξ : ℝ) :
    fourierSymbol cutoffLambda ξ =
    archFourierSymbol (Real.log cutoffLambda) ξ + primeFourierSymbol cutoffLambda ξ :=
  rfl

end
