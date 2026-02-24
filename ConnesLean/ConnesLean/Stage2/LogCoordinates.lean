/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log Coordinates: L² Isometry between R_+* and ℝ

Reference: lamportform.tex, Section 2.

For `g : R_+* → ℂ` supported on `[λ⁻¹, λ]`, define `G = g ∘ exp` on `ℝ`.
Then `G` is supported on `I = (-log λ, log λ)` and the L² norms agree:
  `‖g‖²_{L²(d*x)} = ‖G‖²_{L²(du)}`.

We define `zeroExtend G I` using `Set.indicator` to leverage Mathlib's
measurability and integrability infrastructure for indicator functions.
-/

import ConnesLean.Stage2.TranslationOperator
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ConnesLean

open MeasureTheory Real Set

noncomputable section

/-! ## Log interval and zero extension -/

/-- The symmetric open interval `(-L, L)` in log coordinates.
    When `L = log λ`, this is the support of `G = g ∘ exp` for
    `g` supported on `[λ⁻¹, λ]`. -/
def logInterval (L : ℝ) : Set ℝ := Ioo (-L) L

/-- Zero-extend a function outside a set, using `Set.indicator`.
    `zeroExtend G I u = G u` if `u ∈ I`, and `0` otherwise. -/
def zeroExtend (G : ℝ → ℂ) (I : Set ℝ) : ℝ → ℂ := I.indicator G

@[simp]
theorem zeroExtend_apply_mem {G : ℝ → ℂ} {I : Set ℝ} {u : ℝ} (hu : u ∈ I) :
    zeroExtend G I u = G u :=
  Set.indicator_of_mem hu G

@[simp]
theorem zeroExtend_apply_nmem {G : ℝ → ℂ} {I : Set ℝ} {u : ℝ} (hu : u ∉ I) :
    zeroExtend G I u = 0 :=
  Set.indicator_of_notMem hu G

theorem zeroExtend_eq_indicator (G : ℝ → ℂ) (I : Set ℝ) :
    zeroExtend G I = I.indicator G := rfl

/-- The log interval is a measurable set. -/
theorem measurableSet_logInterval (L : ℝ) : MeasurableSet (logInterval L) :=
  measurableSet_Ioo

/-! ## L² isometry via exp equivalence -/

/-- The L² norm on `(RPos, haarMult)` equals the L² norm on `(ℝ, volume)`
    via the exponential change of variables:
    `∫ ‖g(x)‖² d*x = ∫ ‖g(exp u)‖² du`. -/
theorem lintegral_norm_rpos_eq_real (g : RPos → ℂ) :
    ∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂haarMult =
    ∫⁻ u, ‖g (expToRPos u)‖₊ ^ (2 : ℝ) ∂volume := by
  simp only [haarMult]
  exact lintegral_map_equiv _ expEquivRPos

/-- Translating the dilation norm difference to translation norm difference:
    `∫ ‖g(x) - g(x/a)‖² d*x = ∫ ‖G(u) - G(u - log a)‖² du`
    where `G = g ∘ exp`.

    This is the core identity connecting `‖g - U_a g‖²` to `‖G - S_t G‖²`
    in the additive picture. -/
theorem lintegral_diff_dilation_eq_translation (g : RPos → ℂ) (a : RPos) :
    ∫⁻ x, ‖g x - dilationOp a g x‖₊ ^ (2 : ℝ) ∂haarMult =
    ∫⁻ u, ‖(g ∘ expToRPos) u -
           translationOp (logFromRPos a) (g ∘ expToRPos) u‖₊ ^ (2 : ℝ) ∂volume := by
  -- Transfer from RPos to ℝ via exp equivalence
  have h_eq : ∫⁻ x, ‖g x - dilationOp a g x‖₊ ^ (2 : ℝ) ∂haarMult =
      ∫⁻ u, ‖g (expToRPos u) - dilationOp a g (expToRPos u)‖₊ ^ (2 : ℝ) ∂volume := by
    simp only [haarMult]
    exact lintegral_map_equiv _ expEquivRPos
  rw [h_eq]
  congr 1; ext u
  -- dilationOp a g (exp u) = g(exp u / a) = g(exp(u - log a)) = (g ∘ exp)(u - log a)
  simp only [dilationOp_apply, expToRPos_sub_log, Function.comp, translationOp_apply]

end

end ConnesLean
