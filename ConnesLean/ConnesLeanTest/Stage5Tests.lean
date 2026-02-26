/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 5 Property Tests

Verification tests for Stage 5 definitions and theorems covering
the Fourier symbol and its basic properties.
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real Filter

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

/-! ## SymbolLowerBound tests (Stage 5B) -/

/-- sinh bound: sinh t ≤ t · cosh t for t ≥ 0. -/
example (t : ℝ) (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.cosh t :=
  sinh_le_mul_cosh ht

/-- Weight lower bound: w(t) ≥ 1/(2t) for t ∈ (0,1]. -/
example (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) : 1 / (2 * t) ≤ archWeight t :=
  archWeight_ge_inv_two_t ht ht1

/-- Logarithmic growth of the Fourier symbol. -/
example (Λ : ℝ) (h : 1 < Λ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∃ ξ₀ : ℝ, 2 ≤ ξ₀ ∧
      ∀ ξ : ℝ, ξ₀ ≤ |ξ| → c₁ * Real.log |ξ| - c₂ ≤ fourierSymbol Λ ξ :=
  fourierSymbol_ge_log Λ h

/-- Frequency moment control. -/
example (Λ : ℝ) (h : 1 < Λ) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ ξ : ℝ, Real.log (2 + |ξ|) ≤ a + b * fourierSymbol Λ ξ :=
  frequency_moment_control Λ h

/-- The Fourier symbol tends to +∞. -/
example (Λ : ℝ) (h : 1 < Λ) :
    Tendsto (fun ξ => fourierSymbol Λ ξ) atTop atTop :=
  fourierSymbol_tendsto_atTop Λ h

/-! ## ClosedForm tests (Stage 5C) -/

/-- The zero function belongs to the form domain. -/
example (Λ : ℝ) : (0 : ℝ → ℂ) ∈ formDomain Λ := zero_mem_formDomain Λ

/-- The form domain is nonempty. -/
example (Λ : ℝ) : (formDomain Λ).Nonempty := formDomain_nonempty Λ

/-- Fourier representation of the energy form (axiom instantiation). -/
example (Λ : ℝ) (h : 1 < Λ) (G : ℝ → ℂ) (hG : G ∈ formDomain Λ) :
    (energyForm Λ G).toReal =
    (1 / (2 * Real.pi)) *
    ∫ ξ, fourierSymbol Λ ξ * ‖FourierTransform.fourier G ξ‖ ^ 2 :=
  energyForm_eq_fourierSymbol_integral Λ h G hG

/-- The energy form is closed on L²(ℝ) (axiom instantiation). -/
example (Λ : ℝ) (h : 1 < Λ) : IsClosedEnergyForm Λ :=
  energyForm_closed_on_line Λ h

/-! ## CompactEmbedding tests (Stage 5D) -/

/-- The zero function belongs to any form-norm ball. -/
example (Λ : ℝ) (M : ENNReal) : (0 : ℝ → ℂ) ∈ formNormBall Λ M :=
  zero_mem_formNormBall Λ M

/-- The form-norm ball is nonempty. -/
example (Λ : ℝ) (M : ENNReal) : (formNormBall Λ M).Nonempty :=
  formNormBall_nonempty Λ M

/-- The form-norm ball is monotone in the bound. -/
example (Λ : ℝ) (M M' : ENNReal) (h : M ≤ M') :
    formNormBall Λ M ⊆ formNormBall Λ M' :=
  formNormBall_monotone Λ h

/-- Form-norm ball elements belong to the form domain. -/
example (Λ : ℝ) (M : ENNReal) (hM : M < ⊤) :
    formNormBall Λ M ⊆ formDomain Λ :=
  formNormBall_subset_formDomain Λ hM

/-- Form-norm ball satisfies translation equicontinuity (axiom instantiation). -/
example (Λ : ℝ) (h : 1 < Λ) (M : ENNReal) (hM : M < ⊤) :
    ∀ ε : ENNReal, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ φ ∈ formNormBall Λ M, ∀ t : ℝ,
        |t| < δ → (∫⁻ u, ‖φ (u - t) - φ u‖₊ ^ (2 : ℝ)) < ε :=
  formNormBall_equicontinuous Λ h M hM

/-- The form-norm ball is relatively compact in L². -/
example (Λ : ℝ) (h : 1 < Λ) (M : ENNReal) (hM : M < ⊤) :
    IsRelativelyCompactL2 (formNormBall Λ M) :=
  formNormBall_isRelativelyCompactL2 Λ h M hM

/-! ## CompactResolvent tests (Stage 5E) -/

/-- Kato operator exists (axiom instantiation). -/
example (Λ : ℝ) (h : 1 < Λ) : KatoOperator Λ := kato_operator Λ h

/-- Kato resolvent maps to form domain. -/
example (Λ : ℝ) (h : 1 < Λ) (f : ℝ → ℂ) :
    (kato_operator Λ h).resolvent f ∈ formDomain Λ :=
  kato_resolvent_in_formDomain Λ h f

/-- Resolvent maps bounded functions to form-norm ball. -/
example (Λ : ℝ) (h : 1 < Λ) (f : ℝ → ℂ) (C : ENNReal)
    (hsupp : Function.support f ⊆
      Icc (-(Real.log Λ)) (Real.log Λ))
    (hbdd : (∫⁻ u, ‖f u‖₊ ^ (2 : ℝ)) ≤ C) :
    (kato_operator Λ h).resolvent f ∈ formNormBall Λ C :=
  resolvent_mem_formNormBall Λ (kato_operator Λ h) f hsupp hbdd

/-- Main theorem: A_λ has compact resolvent. -/
example (Λ : ℝ) (h : 1 < Λ) :
    HasCompactResolvent Λ (kato_operator Λ h) :=
  compact_resolvent_of_compact_embedding Λ h

end
