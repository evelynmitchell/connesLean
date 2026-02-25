/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Markov Property for the Energy Form

Reference: lamportform.tex, Section 5, lines 476–479.

The Markov property states that applying a normal contraction `Φ` to the
real-valued function `G` does not increase the energy form:
  `E_λ(Φ ∘ G) ≤ E_λ(G)`

The proof has three layers:
1. **Pointwise**: `‖Φ(a) - Φ(b)‖₊ ≤ ‖a - b‖₊` (Lipschitz), hence `(·)^2` preserves the bound.
2. **Integral**: `lintegral_mono` lifts the pointwise bound to the L² norm integral.
3. **Assembly**: Each `archEnergyIntegrand` and `primeEnergyTerm` has a common weight
   times an lintegral; the weight is unchanged, the lintegral decreases, so each
   term decreases. `Finset.sum_le_sum` and `add_le_add` close the gap.
-/

import ConnesLean.Stage4.NormalContraction
import ConnesLean.Stage2.EnergyForm

namespace ConnesLean

open MeasureTheory Real Set Finset

noncomputable section

/-! ## Layer 1 — Pointwise norm inequality -/

/-- Applying a normal contraction decreases the squared nnnorm (as NNReal):
    `‖Φ(a) - Φ(b)‖₊² ≤ ‖a - b‖₊²`.

    Uses `nnnorm_comp_le` (from NormalContraction.lean) + `NNReal.rpow_le_rpow`. -/
theorem nnnorm_sq_comp_le (hΦ : IsNormalContraction Φ) (a b : ℝ) :
    (‖(↑(Φ a) : ℂ) - ↑(Φ b)‖₊ : NNReal) ^ (2 : ℝ) ≤
    (‖(↑a : ℂ) - ↑b‖₊) ^ (2 : ℝ) :=
  NNReal.rpow_le_rpow (nnnorm_comp_le hΦ a b) (by norm_num)

/-! ## Layer 1.5 — Pointwise bound for zeroExtend + translationOp -/

/-- Pointwise nnnorm bound after `zeroExtend` and `translationOp` rewriting.
    This bridges the abstract `zeroExtend (liftReal ...)` API to pointwise
    indicator values via `zeroExtend_liftReal_comp` and `zeroExtend_liftReal`. -/
theorem nnnorm_zeroExtend_comp_le (hΦ : IsNormalContraction Φ)
    (G : ℝ → ℝ) (I : Set ℝ) (t u : ℝ) :
    ‖zeroExtend (liftReal (Φ ∘ G)) I u -
      translationOp t (zeroExtend (liftReal (Φ ∘ G)) I) u‖₊ ≤
    ‖zeroExtend (liftReal G) I u -
      translationOp t (zeroExtend (liftReal G) I) u‖₊ := by
  rw [zeroExtend_liftReal_comp hΦ, zeroExtend_liftReal]
  simp only [translationOp_apply]
  exact nnnorm_comp_le hΦ (I.indicator G u) (I.indicator G (u - t))

/-! ## Layer 2 — Integral inequality -/

/-- The L² norm integral decreases under a normal contraction:
    `∫ ‖G̃_Φ - S_t G̃_Φ‖₊² ≤ ∫ ‖G̃ - S_t G̃‖₊²` for each fixed `t`. -/
theorem lintegral_nnnorm_sq_comp_le (hΦ : IsNormalContraction Φ)
    (G : ℝ → ℝ) (I : Set ℝ) (t : ℝ) :
    ∫⁻ u, ‖zeroExtend (liftReal (Φ ∘ G)) I u -
           translationOp t (zeroExtend (liftReal (Φ ∘ G)) I) u‖₊ ^ (2 : ℝ) ≤
    ∫⁻ u, ‖zeroExtend (liftReal G) I u -
           translationOp t (zeroExtend (liftReal G) I) u‖₊ ^ (2 : ℝ) := by
  rw [zeroExtend_liftReal_comp hΦ, zeroExtend_liftReal]
  simp only [translationOp_apply]
  apply lintegral_mono
  intro u
  apply ENNReal.rpow_le_rpow
  · exact ENNReal.coe_le_coe.mpr
      (nnnorm_comp_le hΦ (I.indicator G u) (I.indicator G (u - t)))
  · norm_num

/-! ## Layer 3 — Assembly -/

set_option maxHeartbeats 800000 in
-- ENNReal `gcongr` unification is expensive
/-- The archimedean energy integrand decreases under a normal contraction.
    Same weight `(archWeight t).toNNReal`, smaller lintegral. -/
theorem archEnergyIntegrand_comp_le (hΦ : IsNormalContraction Φ)
    (G : ℝ → ℝ) (L t : ℝ) :
    archEnergyIntegrand (liftReal (Φ ∘ G)) L t ≤
    archEnergyIntegrand (liftReal G) L t := by
  simp only [archEnergyIntegrand]
  gcongr
  exact nnnorm_zeroExtend_comp_le hΦ G (logInterval L) _ _

/-- The archimedean energy integral decreases under a normal contraction.
    `lintegral_mono` over the outer `t`-integral. -/
theorem archEnergyIntegral_comp_le (hΦ : IsNormalContraction Φ)
    (G : ℝ → ℝ) (L : ℝ) :
    archEnergyIntegral (liftReal (Φ ∘ G)) L ≤
    archEnergyIntegral (liftReal G) L := by
  unfold archEnergyIntegral
  exact lintegral_mono fun t => archEnergyIntegrand_comp_le hΦ G L t

set_option maxHeartbeats 800000 in
-- ENNReal `gcongr` unification is expensive
/-- Each prime energy term decreases under a normal contraction.
    Same weight `(log p · p^{-m/2}).toNNReal`, smaller lintegral. -/
theorem primeEnergyTerm_comp_le (hΦ : IsNormalContraction Φ)
    (G : ℝ → ℝ) (L : ℝ) (p m : ℕ) :
    primeEnergyTerm p m (liftReal (Φ ∘ G)) L ≤
    primeEnergyTerm p m (liftReal G) L := by
  simp only [primeEnergyTerm]
  gcongr
  exact nnnorm_zeroExtend_comp_le hΦ G (logInterval L) _ _

/-- The total prime energy decreases under a normal contraction.
    `Finset.sum_le_sum` over exponents. -/
theorem totalPrimeEnergy_comp_le (hΦ : IsNormalContraction Φ)
    (G : ℝ → ℝ) (L : ℝ) (p : ℕ) (cutoffLambda : ℝ) :
    totalPrimeEnergy p cutoffLambda (liftReal (Φ ∘ G)) L ≤
    totalPrimeEnergy p cutoffLambda (liftReal G) L := by
  unfold totalPrimeEnergy
  exact Finset.sum_le_sum fun m _ => primeEnergyTerm_comp_le hΦ G L p m

/-! ## Main theorem -/

/-- **Markov property**: The energy form does not increase under normal contractions.

    `E_λ(Φ ∘ G) ≤ E_λ(G)` for any normal contraction `Φ`.

    Reference: lamportform.tex, Section 5, lines 476–479. -/
theorem energyForm_comp_normalContraction_le (hΦ : IsNormalContraction Φ)
    (G : ℝ → ℝ) (cutoffLambda : ℝ) :
    energyForm cutoffLambda (liftReal (Φ ∘ G)) ≤
    energyForm cutoffLambda (liftReal G) := by
  unfold energyForm
  apply add_le_add
  · exact archEnergyIntegral_comp_le hΦ G _
  · exact Finset.sum_le_sum fun p _ =>
      totalPrimeEnergy_comp_le hΦ G _ p cutoffLambda

/-! ## Corollary: absolute value -/

/-- The energy of `|G|` is at most the energy of `G`.
    Special case of the Markov property with `Φ = |·|`.

    Reference: lamportform.tex, line 478. -/
theorem energyForm_abs_le (G : ℝ → ℝ) (cutoffLambda : ℝ) :
    energyForm cutoffLambda (liftReal (fun u => |G u|)) ≤
    energyForm cutoffLambda (liftReal G) := by
  have : (fun u => |G u|) = (fun x => |x|) ∘ G := rfl
  rw [this]
  exact energyForm_comp_normalContraction_le isNormalContraction_abs G cutoffLambda

end

end ConnesLean
