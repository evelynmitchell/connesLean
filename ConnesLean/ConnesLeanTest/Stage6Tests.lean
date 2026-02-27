/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 6 Property Tests

Verification tests for Stage 6 definitions and theorems covering
the indicator energy criterion (Lemma 7).
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real Filter

noncomputable section

/-! ## Energy form component extraction tests -/

/-- Archimedean energy is zero when the full energy form vanishes. -/
example {Λ : ℝ} {G : ℝ → ℂ} (h : energyForm Λ G = 0) :
    archEnergyIntegral G (Real.log Λ) = 0 :=
  archEnergy_eq_zero_of_energyForm_eq_zero h

/-- Each prime energy term is zero when the full energy form vanishes. -/
example {Λ : ℝ} {G : ℝ → ℂ} (h : energyForm Λ G = 0) :
    ∀ p ∈ primeFinset Λ,
      totalPrimeEnergy p Λ G (Real.log Λ) = 0 :=
  primeEnergy_eq_zero_of_energyForm_eq_zero h

/-- Norm-squared integral is zero when weighted integrand vanishes. -/
example {G : ℝ → ℂ} {L t : ℝ} (ht : 0 < t)
    (h : archEnergyIntegrand G L t = 0) :
    ∫⁻ u, ‖zeroExtend G (logInterval L) u -
      translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ)
      ∂volume = 0 :=
  translationOp_normSq_zero_of_weighted_zero ht h

/-! ## Measurability test -/

/-- The archimedean weight (as NNReal) is measurable. -/
example : Measurable (fun t : ℝ => (archWeight t).toNNReal) :=
  measurable_archWeight_ennreal

/-! ## Main theorem test -/

/-- The indicator energy criterion: E_λ(1_B) = 0 implies null or conull. -/
example {Λ : ℝ} {B : Set ℝ} (hΛ : 1 < Λ)
    (hB_meas : MeasurableSet B)
    (hB_sub : B ⊆ logInterval (Real.log Λ))
    (h_energy : energyForm Λ (B.indicator (1 : ℝ → ℂ)) = 0) :
    volume B = 0 ∨ volume (logInterval (Real.log Λ) \ B) = 0 :=
  energyForm_indicator_null_or_conull hΛ hB_meas hB_sub h_energy

end
