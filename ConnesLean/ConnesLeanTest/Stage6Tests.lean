/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 6 Property Tests

Verification tests for Stage 6 definitions and theorems covering
indicator energy (6A), invariance splitting (6B), and constant in domain (6C).
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real Filter

noncomputable section

/-! ## IndicatorEnergy tests (Stage 6A) -/

/-- Indicator-energy criterion: zero energy implies null or conull. -/
example {cutoffLambda : ℝ} {B : Set ℝ} (hLam : 1 < cutoffLambda)
    (hB_meas : MeasurableSet B) (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (h_energy : energyForm cutoffLambda (B.indicator (1 : ℝ → ℂ)) = 0) :
    volume B = 0 ∨ volume (logInterval (Real.log cutoffLambda) \ B) = 0 :=
  energyForm_indicator_null_or_conull hLam hB_meas hB_sub h_energy

/-- Sharpened indicator criterion: zero energy implies null. -/
example {cutoffLambda : ℝ} {B : Set ℝ} (hLam : 1 < cutoffLambda)
    (hB_meas : MeasurableSet B) (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (h_energy : energyForm cutoffLambda (B.indicator (1 : ℝ → ℂ)) = 0) :
    volume B = 0 :=
  energyForm_indicator_null hLam hB_meas hB_sub h_energy

/-- Energy of constant function is positive. -/
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    0 < energyForm cutoffLambda (fun _ => (1 : ℂ)) :=
  energyForm_constant_pos hLam

/-! ## InvarianceSplit tests (Stage 6B) -/

/-- Domain preservation for indicator projection. -/
example (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    ideal.B.indicator G ∈ formDomain cutoffLambda :=
  invariance_domain_preserved cutoffLambda hLam ideal G hG

/-- Energy splitting identity. -/
example (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    energyForm cutoffLambda G =
      energyForm cutoffLambda (ideal.B.indicator G) +
      energyForm cutoffLambda ((logInterval (Real.log cutoffLambda) \ ideal.B).indicator G) :=
  invariance_split cutoffLambda hLam ideal G hG

/-- Domain preservation for complement projection. -/
example (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    (logInterval (Real.log cutoffLambda) \ ideal.B).indicator G ∈ formDomain cutoffLambda :=
  invariance_complement_domain_preserved cutoffLambda hLam ideal G hG

/-! ## ConstantInDomain tests (Stage 6C) -/

/-- Constant function belongs to form domain. -/
example (cutoffLambda : ℝ) :
    (fun _ => (1 : ℂ)) ∈ formDomain cutoffLambda :=
  constant_in_formDomain cutoffLambda

/-- Energy splitting applied to the constant function. -/
example (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) :
    energyForm cutoffLambda (fun _ => (1 : ℂ)) =
      energyForm cutoffLambda (ideal.B.indicator (fun _ => (1 : ℂ))) +
      energyForm cutoffLambda
        ((logInterval (Real.log cutoffLambda) \ ideal.B).indicator (fun _ => (1 : ℂ))) :=
  splitting_applied_to_constant cutoffLambda hLam ideal

/-- Indicator complement sum: f + g = 1̃. -/
example {B : Set ℝ} {L : ℝ} :
    (fun u => zeroExtend (B.indicator (fun _ => (1 : ℂ))) (logInterval L) u +
              zeroExtend ((logInterval L \ B).indicator (fun _ => (1 : ℂ))) (logInterval L) u) =
    zeroExtend (fun _ => (1 : ℂ)) (logInterval L) :=
  indicator_complement_sum

/-- Indicator complement product: f · g = 0. -/
example {B : Set ℝ} {L : ℝ} :
    (fun u => zeroExtend (B.indicator (fun _ => (1 : ℂ))) (logInterval L) u *
              zeroExtend ((logInterval L \ B).indicator (fun _ => (1 : ℂ))) (logInterval L) u) =
    (0 : ℝ → ℂ) :=
  indicator_complement_mul_zero

end
