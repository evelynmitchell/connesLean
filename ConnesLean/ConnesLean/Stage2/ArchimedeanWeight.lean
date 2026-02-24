/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Archimedean Weight and Pointwise Bounds

Reference: lamportform.tex, Section 2, lines 329–332 (w(t) definition),
lines 399–416 (estimates).

The archimedean weight is:
  `w(t) = exp(t/2) / (2 sinh t)`
defined for `t > 0`. This weight appears in the archimedean energy decomposition
  `-W_R(f) = ∫₀^{2L} w(t) ‖G̃ - S_t G̃‖² dt + c_∞(λ) ‖G‖²`

Key estimates:
- `w(t) > 0` for `t > 0`
- `sinh t ≥ t` for `t ≥ 0` (via MVT: `sinh' = cosh ≥ 1`)
- `w(t) ≤ exp(t/2) / (2t)` for `t > 0`
- `2 exp(-t/2) w(t) = 1 / sinh t` (cancellation identity)
- `1/sinh(t) < 4 exp(-t)` for `t ≥ 1`
- (Later) integrability of the correction terms on compact `[0, 2L]` and tail `[2L, ∞)`
-/

import ConnesLean.Stage2.LogCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace ConnesLean

open MeasureTheory Real Set

noncomputable section

/-! ## The archimedean weight function -/

/-- The archimedean weight `w(t) = exp(t/2) / (2 sinh t)`, defined for all `t : ℝ`.
    Meaningful for `t > 0` where `sinh t > 0`.

    Reference: lamportform.tex, line 331. -/
def archWeight (t : ℝ) : ℝ := Real.exp (t / 2) / (2 * Real.sinh t)

/-! ## Auxiliary lemmas -/

/-- `sinh t ≥ t` for `t ≥ 0`, via the mean value theorem:
    `sinh' = cosh ≥ 1` and `sinh 0 = 0`. -/
theorem sinh_ge_self {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.sinh t := by
  have h_diff : Differentiable ℝ Real.sinh := Real.differentiable_sinh
  have h_deriv : ∀ x : ℝ, 1 ≤ deriv Real.sinh x := by
    intro x; rw [Real.deriv_sinh]; exact Real.one_le_cosh x
  have key := mul_sub_le_image_sub_of_le_deriv h_diff h_deriv ht
  simp only [Real.sinh_zero, sub_zero] at key; linarith

/-- `sinh t > 0` for `t > 0`. -/
theorem sinh_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < Real.sinh t := by
  rw [Real.sinh_eq]
  have := Real.exp_strictMono (show -t < t by linarith)
  linarith

/-! ## Positivity and basic bounds -/

/-- The archimedean weight is positive for `t > 0`. -/
theorem archWeight_pos {t : ℝ} (ht : 0 < t) : 0 < archWeight t := by
  unfold archWeight
  apply div_pos
  · exact Real.exp_pos _
  · exact mul_pos (by norm_num) (sinh_pos_of_pos ht)

/-- The key cancellation: `2 exp(-t/2) w(t) = 1 / sinh t`.
    This simplifies the tail integrand in Step 7.2. -/
theorem two_exp_neg_half_mul_archWeight {t : ℝ} (ht : 0 < t) :
    2 * Real.exp (-t / 2) * archWeight t = 1 / Real.sinh t := by
  unfold archWeight
  have hsinh : Real.sinh t ≠ 0 := ne_of_gt (sinh_pos_of_pos ht)
  have h2sinh : 2 * Real.sinh t ≠ 0 := by positivity
  field_simp
  rw [← Real.exp_add]
  simp

/-- `w(t) ≤ exp(t/2) / (2t)` for `t > 0`, using `sinh t ≥ t`. -/
theorem archWeight_le_inv_two_t {t : ℝ} (ht : 0 < t) :
    archWeight t ≤ Real.exp (t / 2) / (2 * t) := by
  unfold archWeight
  exact div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _))
    (mul_pos (by norm_num) ht)
    (mul_le_mul_of_nonneg_left (sinh_ge_self (le_of_lt ht)) (by norm_num))

/-! ## Estimates for the tail integral -/

/-- For `t ≥ 1`, `sinh t > exp t / 4`.
    Since `exp t ≥ 2` for `t ≥ 1`, we get `exp(-t) ≤ 1/2`, and
    `2 sinh t = exp t - exp(-t) > exp t / 2`. -/
theorem sinh_gt_exp_div_four {t : ℝ} (ht : 1 ≤ t) :
    Real.exp t / 4 < Real.sinh t := by
  rw [Real.sinh_eq]
  have h3 : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 2 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  nlinarith [sq_nonneg (Real.exp t), Real.exp_pos (-t)]

/-- For `t ≥ 1`, `1 / sinh t < 4 exp(-t)`. -/
theorem one_div_sinh_lt_four_exp_neg {t : ℝ} (ht : 1 ≤ t) :
    1 / Real.sinh t < 4 * Real.exp (-t) := by
  have hsinh_pos : 0 < Real.sinh t := sinh_pos_of_pos (by linarith)
  rw [div_lt_iff₀ hsinh_pos]
  have h := sinh_gt_exp_div_four ht
  have h_prod : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-t)]

/-! ## Bound on the correction integrand -/

/-- For `t ≥ 0`, `|exp(-t/2) - 1| ≤ t/2`.
    Since `-t/2 ≤ 0`, we have `exp(-t/2) ≤ 1`, and by `add_one_le_exp`,
    `1 - t/2 ≤ exp(-t/2)`. -/
theorem abs_exp_neg_half_sub_one_le {t : ℝ} (ht : 0 ≤ t) :
    |Real.exp (-t / 2) - 1| ≤ t / 2 := by
  have h_le_one : Real.exp (-t / 2) ≤ 1 := by
    calc Real.exp (-t / 2) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  rw [abs_of_nonpos (by linarith)]
  have := Real.add_one_le_exp (-t / 2)
  linarith

/-- The correction integrand `|2(exp(-t/2) - 1) w(t)|` is bounded by
    `exp(t/2) / 2` for `t > 0`, using `|exp(-t/2) - 1| ≤ t/2` and
    `w(t) ≤ exp(t/2)/(2t)`. -/
theorem correction_integrand_bound {t : ℝ} (ht : 0 < t) :
    |2 * (Real.exp (-t / 2) - 1) * archWeight t| ≤ Real.exp (t / 2) / 2 := by
  have h_abs := abs_exp_neg_half_sub_one_le (le_of_lt ht)
  have h_wt := archWeight_le_inv_two_t ht
  have h_wt_pos := le_of_lt (archWeight_pos ht)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg h_wt_pos]
  calc 2 * |Real.exp (-t / 2) - 1| * archWeight t
      ≤ 2 * (t / 2) * (Real.exp (t / 2) / (2 * t)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h_abs (by norm_num))
          h_wt h_wt_pos (by positivity)
    _ = Real.exp (t / 2) / 2 := by field_simp

/-! ## Integrability estimates -/

/-- The tail integrand `1/sinh t` is integrable on `(2L, ∞)` for `L ≥ 1/2`.
    By comparison with `4 exp(-t)` (from `one_div_sinh_lt_four_exp_neg`)
    which is integrable on `(2L, ∞)` (from `integrableOn_exp_neg_Ioi`).

    Reference: lamportform.tex, Step 7.2. -/
theorem arch_tail_integrable {L : ℝ} (hL : 1 / 2 ≤ L) :
    IntegrableOn (fun t => 1 / Real.sinh t) (Ioi (2 * L)) volume := by
  apply Integrable.mono' ((integrableOn_exp_neg_Ioi (2 * L)).const_mul 4)
  · exact (measurable_const.div Real.measurable_sinh).aestronglyMeasurable.restrict
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun t ht => by
      simp only [mem_Ioi] at ht
      have h1 : 1 ≤ t := by linarith
      have hsinh_pos : 0 < Real.sinh t := sinh_pos_of_pos (by linarith)
      rw [Real.norm_of_nonneg (div_nonneg (by norm_num) (le_of_lt hsinh_pos))]
      exact le_of_lt (one_div_sinh_lt_four_exp_neg h1)

/-- The correction integrand `2(exp(-t/2) - 1) w(t)` is integrable on `(0, 2L]`.
    By `correction_integrand_bound`, the integrand is bounded by `exp(t/2)/2`
    for each `t`, and on `Ioc 0 (2L)` we have `t ≤ 2L`, so `t/2 ≤ L` and hence
    `exp(t/2) ≤ exp(L)`. Thus the integrand is uniformly bounded by `exp(L)/2`
    on this finite-measure set.

    Reference: lamportform.tex, Step 8.2. -/
theorem arch_correction_integrable {L : ℝ} (_hL : 0 < L) :
    IntegrableOn (fun t => 2 * (Real.exp (-t / 2) - 1) * archWeight t)
      (Ioc 0 (2 * L)) volume := by
  refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ (Real.exp L / 2) ?_
  · exact ((measurable_const.mul
      ((Real.measurable_exp.comp (measurable_neg.div_const 2)).sub measurable_const)).mul
      ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
        (measurable_const.mul Real.measurable_sinh))).aestronglyMeasurable.restrict
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun t ht => by
      simp only [mem_Ioc] at ht
      have h_bound := correction_integrand_bound ht.1
      calc ‖2 * (Real.exp (-t / 2) - 1) * archWeight t‖
          = |2 * (Real.exp (-t / 2) - 1) * archWeight t| := Real.norm_eq_abs _
        _ ≤ Real.exp (t / 2) / 2 := h_bound
        _ ≤ Real.exp L / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact Real.exp_le_exp.mpr (by linarith [ht.2])

/-- The map `t ↦ ‖G̃ - S_t G̃‖²` is measurable as a function of `t`.
    This is a prerequisite for the outer integral in the energy decomposition
    to type-check. Follows from measurability of `translationOp` in `t` and
    measurability of the Lebesgue integral. -/
theorem measurable_archEnergyIntegrand {G : ℝ → ℂ} (hG : Measurable G) (L : ℝ) :
    Measurable (fun t => ∫⁻ u, ‖zeroExtend G (logInterval L) u -
      translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ) ∂volume) := by
  apply Measurable.lintegral_prod_right
  have h_ze : Measurable (zeroExtend G (logInterval L)) :=
    Measurable.indicator hG (measurableSet_logInterval L)
  exact (((h_ze.comp measurable_snd).sub
    (h_ze.comp (measurable_snd.sub measurable_fst))).nnnorm.coe_nnreal_ennreal.pow_const _)

/-! ## Archimedean energy integrand -/

/-- The archimedean energy integrand:
    `w(t) * ‖G̃ - S_t G̃‖²` as an ENNReal-valued function of `t`.

    This is the integrand in the archimedean energy decomposition. -/
def archEnergyIntegrand (G : ℝ → ℂ) (L : ℝ) (t : ℝ) : ENNReal :=
  ↑(archWeight t).toNNReal *
  ∫⁻ u, ‖zeroExtend G (logInterval L) u -
         translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ)
         ∂volume

/-- The archimedean energy integral on `(0, 2L)`:
    `∫₀^{2L} w(t) ‖G̃ - S_t G̃‖² dt`. -/
def archEnergyIntegral (G : ℝ → ℂ) (L : ℝ) : ENNReal :=
  ∫⁻ t in Ioo 0 (2 * L), archEnergyIntegrand G L t ∂volume

/-! ## The archimedean constant -/

/-- The archimedean constant `c_∞(λ)`:
    `c_∞(λ) = -(log 4π + γ) + ∫₀^{2L} 2(e^{-t/2} - 1) w(t) dt
                                + ∫_{2L}^∞ 2 e^{-t/2} w(t) dt`,
    where `L = log cutoffLambda`.

    This definition matches the expression used in lamportform.tex
    (Steps 7.2, 8.2, and 9, around line ~420); analytic convergence of
    the two integrals is treated there and in subsequent lemmas. -/
def archConstant (cutoffLambda : ℝ) : ℝ :=
  let L := Real.log cutoffLambda
  let emConst := Real.eulerMascheroniConstant
  let correction := ∫ t in Ioc 0 (2 * L),
    2 * (Real.exp (-t / 2) - 1) * archWeight t
  let tail := ∫ t in Ici (2 * L),
    2 * Real.exp (-t / 2) * archWeight t
  (-(Real.log (4 * Real.pi) + emConst) + correction + tail)

end

end ConnesLean
