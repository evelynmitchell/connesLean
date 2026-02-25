/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 3 Property Tests

Verification tests for Stage 3 (Energy Decomposition) definitions and theorems
covering prime distributions, archimedean weights, archimedean distribution,
and the energy form E_λ(G).
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real

noncomputable section

/-! ## PrimeDistribution tests -/

/-- primeBound unfolds to Nat.floor of λ². -/
example (cutoffLambda : ℝ) : primeBound cutoffLambda = ⌊cutoffLambda ^ 2⌋₊ := rfl

/-- primeFinset filters primes from range of primeBound. -/
example (cutoffLambda : ℝ) :
    primeFinset cutoffLambda = (Finset.range (primeBound cutoffLambda + 1)).filter Nat.Prime :=
  rfl

/-- primeConstant is nonpositive for primes when λ > 1. -/
example {p : ℕ} (hp : Nat.Prime p) {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    primeConstant p cutoffLambda ≤ 0 :=
  primeConstant_nonpos hp hLam

/-! ## ArchimedeanWeight tests -/

/-- archWeight is positive for t > 0. -/
example {t : ℝ} (ht : 0 < t) : 0 < archWeight t :=
  archWeight_pos ht

/-- sinh(t) ≥ t for t ≥ 0. -/
example {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.sinh t :=
  sinh_ge_self ht

/-- sinh is positive for positive input. -/
example {t : ℝ} (ht : 0 < t) : 0 < Real.sinh t :=
  sinh_pos_of_pos ht

/-- archWeight upper bound: w(t) ≤ e^{t/2}/(2t). -/
example {t : ℝ} (ht : 0 < t) : archWeight t ≤ Real.exp (t / 2) / (2 * t) :=
  archWeight_le_inv_two_t ht

/-- sinh(t) > e^t/4 for t ≥ 1. -/
example {t : ℝ} (ht : 1 ≤ t) : Real.exp t / 4 < Real.sinh t :=
  sinh_gt_exp_div_four ht

/-- 1/sinh(t) < 4e^{-t} for t ≥ 1. -/
example {t : ℝ} (ht : 1 ≤ t) : 1 / Real.sinh t < 4 * Real.exp (-t) :=
  one_div_sinh_lt_four_exp_neg ht

/-- |e^{-t/2} - 1| ≤ t/2 for t ≥ 0. -/
example {t : ℝ} (ht : 0 ≤ t) : |Real.exp (-t / 2) - 1| ≤ t / 2 :=
  abs_exp_neg_half_sub_one_le ht

/-- Correction integrand bound: |2(e^{-t/2}-1)w(t)| ≤ e^{t/2}/2. -/
example {t : ℝ} (ht : 0 < t) :
    |2 * (Real.exp (-t / 2) - 1) * archWeight t| ≤ Real.exp (t / 2) / 2 :=
  correction_integrand_bound ht

/-- Tail integral 1/sinh is integrable on (2L, ∞). -/
example {L : ℝ} (hL : 1 / 2 ≤ L) :
    IntegrableOn (fun t => 1 / Real.sinh t) (Ioi (2 * L)) MeasureTheory.volume :=
  arch_tail_integrable hL

/-- Correction term is integrable on (0, 2L]. -/
example {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun t => 2 * (Real.exp (-t / 2) - 1) * archWeight t)
      (Ioc 0 (2 * L)) MeasureTheory.volume :=
  arch_correction_integrable hL

/-- The arch energy integrand is measurable. -/
example {G : ℝ → ℂ} (hG : Measurable G) (L : ℝ) :
    Measurable (fun t => ∫⁻ u,
      ‖zeroExtend G (logInterval L) u -
       translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ)
      ∂MeasureTheory.volume) :=
  measurable_archEnergyIntegrand hG L

/-! ## ArchimedeanDistribution tests -/

/-- expToRPos negation: exp(-t) = (exp(t))⁻¹. -/
example (t : ℝ) : expToRPos (-t) = (expToRPos t)⁻¹ :=
  expToRPos_neg t

/-- Archimedean distribution of zero function is zero. -/
example : archDistribution 0 = 0 :=
  archDistribution_zero

/-! ## EnergyForm tests -/

/-- Energy form is nonneg. -/
example (cutoffLambda : ℝ) (G : ℝ → ℂ) :
    (0 : ENNReal) ≤ energyForm cutoffLambda G :=
  energyForm_nonneg cutoffLambda G

/-- Energy form of zero function is zero. -/
example (cutoffLambda : ℝ) : energyForm cutoffLambda 0 = 0 :=
  energyForm_zero cutoffLambda

/-- zeroExtend of zero function is zero. -/
example (I : Set ℝ) : zeroExtend 0 I = 0 :=
  zeroExtend_zero I

/-- Sum of prime constants is nonpositive when λ > 1. -/
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    ∑ p ∈ primeFinset cutoffLambda, primeConstant p cutoffLambda ≤ 0 :=
  totalCorrection_prime_nonpos hLam

end
