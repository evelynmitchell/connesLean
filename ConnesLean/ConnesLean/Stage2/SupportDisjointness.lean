/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Support Disjointness and Orthogonality

Reference: lamportform.tex, Section 2, Remark 2.

When `t > 2L`, the intervals `(-L, L)` and `(-L + t, L + t)` are disjoint,
so `zeroExtend G I` and `translationOp t (zeroExtend G I)` have disjoint support.
This gives the Pythagorean identity:
  `‖G̃ - S_t G̃‖² = ‖G̃‖² + ‖S_t G̃‖² = 2‖G‖²`
which saturates the bound from Lemma 2 (the unitary identity).
-/

import ConnesLean.Stage2.LogCoordinates
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace ConnesLean

open MeasureTheory Real Set

noncomputable section

/-! ## Interval disjointness -/

/-- When `t > 2 * L` and `L > 0`, the intervals `(-L, L)` and `(-L + t, L + t)` are disjoint.
    This is because the right endpoint of `(-L, L)` is `L`, while the left endpoint
    of `(-L + t, L + t)` is `-L + t > -L + 2L = L`. -/
theorem Ioo_disjoint_shift {L t : ℝ} (_hL : 0 < L) (ht : 2 * L < t) :
    Disjoint (Ioo (-L) L) (Ioo (-L + t) (L + t)) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  -- x ∈ (-L, L) means x < L
  -- x ∈ (-L + t, L + t) means -L + t < x
  have h1 : x < L := hx1.2
  have h2 : -L + t < x := hx2.1
  linarith

/-- The support of `translationOp t (zeroExtend G I)` is contained in the shifted interval.
    Specifically, if `I = Ioo a b`, then `translationOp t (zeroExtend G I)` vanishes
    outside `Ioo (a + t) (b + t)`. -/
theorem translationOp_zeroExtend_eq_zero {G : ℝ → ℂ} {a b t u : ℝ}
    (hu : u ∉ Ioo (a + t) (b + t)) :
    translationOp t (zeroExtend G (Ioo a b)) u = 0 := by
  simp only [translationOp_apply]
  apply zeroExtend_apply_nmem
  intro ⟨h1, h2⟩
  exact hu ⟨by linarith, by linarith⟩

/-! ## Pointwise product vanishing and norm identities -/

/-- When `t > 2L` and `L > 0`, the zero-extended function and its translation
    have disjoint support. Their pointwise product vanishes everywhere. -/
theorem pointwise_mul_zero_of_large_shift {G : ℝ → ℂ} {L t : ℝ}
    (_hL : 0 < L) (ht : 2 * L < t) (u : ℝ) :
    zeroExtend G (logInterval L) u *
    starRingEnd ℂ (translationOp t (zeroExtend G (logInterval L)) u) = 0 := by
  -- Either u ∈ logInterval L or u ∉ logInterval L
  by_cases hu : u ∈ logInterval L
  · -- u ∈ (-L, L), so u - t ∉ (-L, L) since u - t < L - t < L - 2L = -L
    have hu_shift : u - t ∉ logInterval L := by
      simp only [logInterval, mem_Ioo] at hu ⊢
      intro ⟨h1, _⟩
      linarith [hu.2]
    simp [translationOp_apply, zeroExtend_apply_nmem hu_shift]
  · -- u ∉ (-L, L), so zeroExtend G I u = 0
    simp [zeroExtend_apply_nmem hu]

/-- The L² norm of `zeroExtend G I - translationOp t (zeroExtend G I)` when `t > 2L`:
    the squared norm of the difference equals the sum of squared norms
    (Pythagorean identity from disjoint support).

    `‖G̃ - S_t G̃‖² = ‖G̃‖² + ‖S_t G̃‖²` -/
theorem lintegral_norm_sub_eq_add_of_large_shift {G : ℝ → ℂ} {L t : ℝ}
    (_hL : 0 < L) (ht : 2 * L < t) (hG : Measurable G) :
    ∫⁻ u, ‖zeroExtend G (logInterval L) u -
           translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ) ∂volume =
    ∫⁻ u, ‖zeroExtend G (logInterval L) u‖₊ ^ (2 : ℝ) ∂volume +
    ∫⁻ u, ‖translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ) ∂volume := by
  -- Pointwise: when supports are disjoint, ‖a - b‖² = ‖a‖² + ‖b‖²
  -- because at each point, exactly one of a, b is zero
  have h_pw : ∀ u,
      ↑‖zeroExtend G (logInterval L) u -
        translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ) =
      (↑‖zeroExtend G (logInterval L) u‖₊ ^ (2 : ℝ) +
       ↑‖translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ) :
        ENNReal) := by
    intro u
    by_cases hu : u ∈ logInterval L
    · -- u ∈ I: the translated function vanishes at u
      have hu_shift : u - t ∉ logInterval L := by
        simp only [logInterval, mem_Ioo] at hu ⊢
        intro ⟨h1, _⟩; linarith [hu.2]
      simp [translationOp_apply, zeroExtend_apply_nmem hu_shift, sub_zero]
    · -- u ∉ I: the original function vanishes at u
      simp [zeroExtend_apply_nmem hu]
  simp_rw [h_pw]
  -- Split integral of sum into sum of integrals
  -- Need: Measurable (fun u => (↑‖zeroExtend G I u‖₊)^2 : ℝ → ENNReal)
  have h_meas_ze : Measurable (zeroExtend G (logInterval L)) :=
    Measurable.indicator hG (measurableSet_logInterval L)
  exact lintegral_add_left (h_meas_ze.nnnorm.coe_nnreal_ennreal.pow_const _) _

/-- When `t > 2L`, the squared norm of the translated function equals the original:
    `‖S_t G̃‖² = ‖G̃‖²`, by translation invariance of Lebesgue measure.
    Combined with the Pythagorean identity, this gives `‖G̃ - S_t G̃‖² = 2‖G̃‖²`. -/
theorem lintegral_norm_translationOp_zeroExtend (t : ℝ) (G : ℝ → ℂ) (I : Set ℝ) :
    ∫⁻ u, ‖translationOp t (zeroExtend G I) u‖₊ ^ (2 : ℝ) ∂volume =
    ∫⁻ u, ‖zeroExtend G I u‖₊ ^ (2 : ℝ) ∂volume :=
  translationOp_lintegral_norm_eq t (zeroExtend G I)

end

end ConnesLean
