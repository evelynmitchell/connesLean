/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 2 Property Tests

Verification tests for Stage 2 definitions and theorems covering
translation operators, log coordinates, and support disjointness.
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real

noncomputable section

/-! ## TranslationOperator tests -/

/-- Translation by 0 is the identity. -/
example (φ : ℝ → ℂ) : translationOp 0 φ = φ :=
  translationOp_zero φ

/-- Translation applies correctly: (S_t φ)(u) = φ(u - t). -/
example (t : ℝ) (φ : ℝ → ℂ) (u : ℝ) : translationOp t φ u = φ (u - t) :=
  translationOp_apply t φ u

/-- Translation semigroup law: S_s ∘ S_t = S_{s+t}. -/
example (s t : ℝ) (φ : ℝ → ℂ) :
    translationOp s (translationOp t φ) = translationOp (s + t) φ :=
  translationOp_add s t φ

/-- Dilation in multiplicative coords = translation in log coords. -/
example (t : ℝ) (g : RPos → ℂ) (u : ℝ) :
    dilationOp (expToRPos t) g (expToRPos u) =
    translationOp t (g ∘ expToRPos) u :=
  dilation_eq_translation t g u

/-- Translation preserves L² norm (lintegral version). -/
example (t : ℝ) (φ : ℝ → ℂ) :
    ∫⁻ u, ‖translationOp t φ u‖₊ ^ (2 : ℝ) ∂MeasureTheory.volume =
    ∫⁻ u, ‖φ u‖₊ ^ (2 : ℝ) ∂MeasureTheory.volume :=
  translationOp_lintegral_norm_eq t φ

/-! ## LogCoordinates tests -/

/-- logInterval is measurable. -/
example (L : ℝ) : MeasurableSet (logInterval L) :=
  measurableSet_logInterval L

/-- zeroExtend agrees with Set.indicator. -/
example (G : ℝ → ℂ) (I : Set ℝ) : zeroExtend G I = I.indicator G :=
  zeroExtend_eq_indicator G I

/-- zeroExtend returns G(u) when u ∈ I. -/
example {G : ℝ → ℂ} {I : Set ℝ} {u : ℝ} (hu : u ∈ I) :
    zeroExtend G I u = G u :=
  zeroExtend_apply_mem hu

/-- zeroExtend returns 0 when u ∉ I. -/
example {G : ℝ → ℂ} {I : Set ℝ} {u : ℝ} (hu : u ∉ I) :
    zeroExtend G I u = 0 :=
  zeroExtend_apply_nmem hu

/-- L² norm transfers from RPos to ℝ via exp. -/
example (g : RPos → ℂ) :
    ∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂haarMult =
    ∫⁻ u, ‖g (expToRPos u)‖₊ ^ (2 : ℝ) ∂MeasureTheory.volume :=
  lintegral_norm_rpos_eq_real g

/-- Dilation difference norm = translation difference norm in log coords. -/
example (g : RPos → ℂ) (a : RPos) :
    ∫⁻ x, ‖g x - dilationOp a g x‖₊ ^ (2 : ℝ) ∂haarMult =
    ∫⁻ u, ‖(g ∘ expToRPos) u - translationOp (logFromRPos a) (g ∘ expToRPos) u‖₊ ^ (2 : ℝ)
      ∂MeasureTheory.volume :=
  lintegral_diff_dilation_eq_translation g a

/-! ## SupportDisjointness tests -/

/-- Shifted intervals are disjoint when shift > 2L. -/
example {L t : ℝ} (hL : 0 < L) (ht : 2 * L < t) :
    Disjoint (Ioo (-L) L) (Ioo (-L + t) (L + t)) :=
  Ioo_disjoint_shift hL ht

/-- Translation of zero-extended function vanishes outside shifted interval. -/
example {G : ℝ → ℂ} {a b t u : ℝ} (hu : u ∉ Ioo (a + t) (b + t)) :
    translationOp t (zeroExtend G (Ioo a b)) u = 0 :=
  translationOp_zeroExtend_eq_zero hu

/-- Pointwise product vanishes for large shifts (orthogonality). -/
example {G : ℝ → ℂ} {L t : ℝ} (hL : 0 < L) (ht : 2 * L < t) (u : ℝ) :
    zeroExtend G (logInterval L) u *
    (starRingEnd ℂ) (translationOp t (zeroExtend G (logInterval L)) u) = 0 :=
  pointwise_mul_zero_of_large_shift hL ht u

/-- Translation preserves L² norm of zero-extended functions. -/
example (t : ℝ) (G : ℝ → ℂ) (I : Set ℝ) :
    ∫⁻ u, ‖translationOp t (zeroExtend G I) u‖₊ ^ (2 : ℝ) ∂MeasureTheory.volume =
    ∫⁻ u, ‖zeroExtend G I u‖₊ ^ (2 : ℝ) ∂MeasureTheory.volume :=
  lintegral_norm_translationOp_zeroExtend t G I

end
