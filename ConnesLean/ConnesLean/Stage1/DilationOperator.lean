/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dilation Operator on L²(R_+*, d*x)

Reference: lamportform.tex, Section 1, lines 110-119, equation (1).

For `a > 0`, the dilation operator is defined by `(U_a g)(x) = g(x/a)`.
It is unitary on L^2(R_+*, d*x):
- Isometric: ||U_a g||_2 = ||g||_2 by Haar invariance d*(x/a) = d*x
- Surjective: U_a^{-1} = U_{a^{-1}}
By Cauchy-Schwarz + isometry: |<g, U_a g>| <= ||g||_2^2.

## Inner product convention
See `ConnesLean.Common.Notation` for the convention on inner products.
-/

import ConnesLean.Stage1.MultiplicativeHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Function.L1Space.Integrable

namespace ConnesLean

open MeasureTheory

noncomputable section

/-- The dilation operator `U_a` on functions `RPos -> C`, defined by
    `(U_a g)(x) = g(x / a)` for `a in R_+*`.

    Reference: lamportform.tex, equation (1): `(U_a g)(x) := g(x/a)` for `a > 0`. -/
def dilationOp (a : RPos) (g : RPos -> ℂ) : RPos -> ℂ :=
  fun x => g (x / a)

@[simp]
theorem dilationOp_apply (a : RPos) (g : RPos -> ℂ) (x : RPos) :
    dilationOp a g x = g (x / a) := rfl

/-- Dilation at `1` is the identity. -/
@[simp]
theorem dilationOp_one (g : RPos -> ℂ) : dilationOp 1 g = g := by
  ext x
  simp only [dilationOp_apply]
  congr 1
  ext
  exact div_one x.val

/-- Dilation is multiplicative: `U_a . U_b = U_{ab}`. -/
theorem dilationOp_mul (a b : RPos) (g : RPos -> ℂ) :
    dilationOp a (dilationOp b g) = dilationOp (a * b) g := by
  ext x
  simp only [dilationOp_apply]
  congr 1
  ext
  simp [RPos.div_val, div_div]

/-- `U_{a^{-1}}` is the inverse of `U_a`. -/
theorem dilationOp_inv (a : RPos) (g : RPos -> ℂ) :
    dilationOp a⁻¹ (dilationOp a g) = g := by
  ext x
  simp only [dilationOp_apply]
  congr 1
  ext
  simp only [RPos.div_val, RPos.inv_val]
  rw [div_div]
  rw [show a.val⁻¹ * a.val = 1 from inv_mul_cancel₀ (RPos.toReal_ne_zero a)]
  exact div_one x.val

/-- The dilation operator is isometric on L^2(d*x): ||U_a g||_2 = ||g||_2.
    This follows from Haar invariance: d*(x/a) = d*x.

    Reference: lamportform.tex, line 115-116. -/
theorem dilationOp_norm_eq (a : RPos) (g : RPos -> ℂ)
    (_hg : MemLp g 2 haarMult) :
    ∫⁻ x, ‖dilationOp a g x‖₊ ^ (2 : ℝ) ∂haarMult =
    ∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂haarMult := by
  simp only [dilationOp_apply, haarMult]
  -- Transfer both integrals from RPos to ℝ via the exp equivalence
  -- (use `exact` not `rw` to handle the expToRPos ↔ ⇑expEquivRPos coercion)
  have lhs_eq : ∫⁻ x, ‖g (x / a)‖₊ ^ (2 : ℝ) ∂Measure.map expToRPos volume =
      ∫⁻ u, ‖g (expToRPos u / a)‖₊ ^ (2 : ℝ) ∂volume :=
    lintegral_map_equiv _ expEquivRPos
  have rhs_eq : ∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂Measure.map expToRPos volume =
      ∫⁻ u, ‖g (expToRPos u)‖₊ ^ (2 : ℝ) ∂volume :=
    lintegral_map_equiv _ expEquivRPos
  rw [lhs_eq, rhs_eq]
  -- Conjugation: expToRPos u / a = expToRPos (u - log a)
  simp_rw [expToRPos_sub_log]
  -- Rewrite subtraction as negative addition for translation invariance
  simp_rw [sub_eq_add_neg, add_comm _ (-logFromRPos a)]
  -- Apply Lebesgue translation invariance: ∫⁻ f(c + x) dx = ∫⁻ f(x) dx
  exact lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
    (fun v => ↑‖g (expToRPos v)‖₊ ^ (2 : ℝ)) (-logFromRPos a)

/-- The Cauchy-Schwarz bound: |<g, U_a g>| <= ||g||_2^2.

    Reference: lamportform.tex, line 118-119:
    |<g, U_a g>| <= ||g||_2 * ||U_a g||_2 = ||g||_2^2. -/
theorem inner_dilationOp_le (a : RPos) (g : RPos -> ℂ)
    (hg : MemLp g 2 haarMult) :
    ‖∫ x, g x * starRingEnd ℂ (dilationOp a g x) ∂haarMult‖ ≤
    (∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂haarMult).toReal := by
  -- Build MeasurableEquiv for (· / a) on RPos
  let divEquiv : RPos ≃ᵐ RPos := {
    toEquiv := {
      toFun := (· / a)
      invFun := (· * a)
      left_inv := fun y => by
        ext; simp [RPos.div_val, div_mul_cancel₀ _ a.2.ne']
      right_inv := fun y => by
        ext; simp [RPos.div_val, mul_div_cancel_right₀ _ a.2.ne']
    }
    measurable_toFun := (measurable_subtype_coe.div_const a.val).subtype_mk
    measurable_invFun := (measurable_subtype_coe.mul_const a.val).subtype_mk
  }
  -- MeasurePreserving for (· / a)
  have h_mp : MeasurePreserving divEquiv haarMult haarMult := ⟨divEquiv.measurable, by
    simp only [haarMult]
    rw [Measure.map_map divEquiv.measurable measurable_expToRPos,
        show (⇑divEquiv : RPos → RPos) ∘ expToRPos = expToRPos ∘ (· - logFromRPos a) from
          funext (fun u => expToRPos_sub_log u a),
        ← Measure.map_map measurable_expToRPos (measurable_sub_const _)]
    congr 1
    have : (· - logFromRPos a : ℝ → ℝ) = ((-logFromRPos a) + ·) := by funext x; ring
    rw [this]
    exact map_add_left_eq_self volume (-logFromRPos a)⟩
  -- Integrability: g * star(g) is integrable by Hölder (L²×L² → L¹)
  have h_int_prod : Integrable (fun x => g x * star (g x)) haarMult :=
    hg.integrable_mul hg.star
  -- Hence ‖g‖² is integrable (since ‖g x * star(g x)‖ = ‖g x‖²)
  have h_int_sq : Integrable (fun x : RPos => ‖g x‖ ^ 2) haarMult :=
    Integrable.congr h_int_prod.norm (Filter.Eventually.of_forall fun x => by
      change ‖g x * star (g x)‖ = ‖g x‖ ^ 2
      rw [norm_mul, norm_star, ← sq])
  -- ‖g(·/a)‖² is integrable by measure preservation
  have h_int_sq_a : Integrable (fun x : RPos => ‖g (x / a)‖ ^ 2) haarMult :=
    h_mp.integrable_comp_of_integrable h_int_sq
  -- Main calc chain
  calc ‖∫ x, g x * starRingEnd ℂ (dilationOp a g x) ∂haarMult‖
    -- Step 1: Triangle inequality
      ≤ ∫ x, ‖g x * starRingEnd ℂ (dilationOp a g x)‖ ∂haarMult :=
        norm_integral_le_integral_norm _
    -- Step 2: Pointwise ‖g·conj(g(·/a))‖ = ‖g‖·‖g(·/a)‖
    _ = ∫ x, ‖g x‖ * ‖g (x / a)‖ ∂haarMult := by
        congr 1; ext x
        rw [dilationOp_apply, norm_mul, starRingEnd_apply, norm_star]
    -- Step 3: AM-GM pointwise: ab ≤ (a² + b²)/2
    _ ≤ ∫ x, (‖g x‖ ^ 2 + ‖g (x / a)‖ ^ 2) / 2 ∂haarMult := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
        · exact (h_int_sq.add h_int_sq_a).div_const 2
        · exact Filter.Eventually.of_forall fun x => by
            nlinarith [sq_nonneg (‖g x‖ - ‖g (x / a)‖), sq_abs ‖g x‖, sq_abs ‖g (x / a)‖]
    -- Step 4: Split integral: ∫(f+g)/2 = (∫f + ∫g)/2
    _ = (∫ x, ‖g x‖ ^ 2 ∂haarMult + ∫ x, ‖g (x / a)‖ ^ 2 ∂haarMult) / 2 := by
        rw [integral_div, integral_add h_int_sq h_int_sq_a]
    -- Step 5: Change of variables: ∫ ‖g(·/a)‖² = ∫ ‖g‖²
    _ = (∫ x, ‖g x‖ ^ 2 ∂haarMult + ∫ x, ‖g x‖ ^ 2 ∂haarMult) / 2 := by
        congr 1; congr 1
        have h_eq : ∀ y : RPos, ⇑divEquiv y = y / a := fun _ => rfl
        simp_rw [show ∀ x : RPos, ‖g (x / a)‖ ^ 2 = ‖g (⇑divEquiv x)‖ ^ 2 from
          fun x => by rw [h_eq]]
        exact h_mp.integral_comp' (fun x => ‖g x‖ ^ 2)
    -- Step 6: (T + T) / 2 = T
    _ = ∫ x, ‖g x‖ ^ 2 ∂haarMult := by ring
    -- Step 7: Convert Bochner integral to lintegral
    _ = (∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂haarMult).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun x => sq_nonneg _)
          (hg.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable]
        congr 1; apply lintegral_congr; intro x
        have h_two : (2 : ℝ) = ((2 : ℕ) : ℝ) := by simp
        rw [← Real.rpow_natCast _ 2, ← h_two,
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, ofReal_norm_eq_enorm]
        norm_cast

end

end ConnesLean
