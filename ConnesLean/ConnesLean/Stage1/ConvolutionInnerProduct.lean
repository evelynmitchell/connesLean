/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma 1: Convolution Inner-Product Identity

Reference: lamportform.tex, Lemma 1.1 (`lem:f-inner`), lines 122–163.

For `f = g ⋆ g*` and `a > 0`:
1. `f(a) = ⟨g, U_a g⟩_{L²(d*x)}`
2. `f(a⁻¹) = conj(f(a))`
3. `f(a) + f(a⁻¹) = 2 Re⟨g, U_a g⟩`
4. `f(1) = ‖g‖²`

## Inner product convention
The paper uses `⟨g, h⟩ = ∫ g(y) conj(h(y)) d*y` (conjugate-linear in second).
Mathlib uses `⟪x, y⟫` (conjugate-linear in first, linear in second).
Paper's `⟨g, U_a g⟩ = Mathlib's ⟪U_a g, g⟫ = conj(⟪g, U_a g⟫)`.
For real parts this distinction vanishes: `Re⟨g, U_a g⟩_paper = Re⟪g, U_a g⟫_Mathlib`.
-/

import ConnesLean.Stage1.DilationOperator
import ConnesLean.Stage1.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace ConnesLean

open MeasureTheory Complex

noncomputable section

/-- **Lemma 1, Part 1**: `f(a) = ⟨g, U_a g⟩_{L²(d*x)}`.

    The self-convolution `(g ⋆ g*)(a)` equals the inner product of `g`
    with its dilation `U_a g`.

    Reference: lamportform.tex, Step 1 (lines 134–149).

    Proof: Unfold convolution, apply involution definition,
    recognize as inner product with dilation operator. -/
theorem convolution_eq_inner (g : RPos → ℂ) (a : RPos) :
    mulConv g (mulInvol g) a =
    ∫ y, g y * starRingEnd ℂ (dilationOp a g y) ∂haarMult := by
  rw [mulConv_mulInvol_apply]
  -- The integrands are the same since dilationOp a g y = g (y / a)
  rfl

/-- **Lemma 1, Part 2**: `f(a⁻¹) = conj(f(a))`.

    Reference: lamportform.tex, Step 2 (lines 150–156).

    Proof: Replace `a` by `a⁻¹`, substitute `y' = ya` using Haar invariance. -/
theorem convolution_inv_eq_conj (g : RPos → ℂ) (a : RPos)
    (_hg : MemLp g 2 haarMult) :
    mulConv g (mulInvol g) a⁻¹ = starRingEnd ℂ (mulConv g (mulInvol g) a) := by
  -- Expand both sides using mulConv_mulInvol_apply
  rw [mulConv_mulInvol_apply, mulConv_mulInvol_apply]
  -- Step 1: Simplify y / a⁻¹ = y * a on LHS
  simp_rw [show ∀ y : RPos, y / a⁻¹ = y * a from fun y => by
    ext; simp [RPos.div_val, RPos.inv_val]]
  -- Step 2: Pull conj through RHS integral: conj(∫ f) = ∫ conj(f)
  rw [← integral_conj]
  -- Step 3: Simplify conj(g(y) * conj(g(y/a))) = conj(g(y)) * g(y/a)
  simp_rw [show ∀ y : RPos, (starRingEnd ℂ) (g y * (starRingEnd ℂ) (g (y / a))) =
      (starRingEnd ℂ) (g y) * g (y / a) from fun y => by
    rw [map_mul]; congr 1; exact star_star (g (y / a))]
  -- Goal: ∫ g(y) * conj(g(y*a)) d*y = ∫ conj(g(y)) * g(y/a) d*y
  -- Step 4: Use the shared division equivalence and measure preservation
  have h_mp : MeasurePreserving (rpDivEquiv a) haarMult haarMult :=
    measurePreserving_rpDiv a
  -- Step 5: Change of variables y ↦ y/a on LHS via integral_comp'
  -- ← integral_comp' rewrites ∫ h(y) d*y to ∫ h(y/a) d*y
  rw [← h_mp.integral_comp' (fun y => g y * (starRingEnd ℂ) (g (y * a)))]
  -- Unfold rpDivEquiv (y/a) and simplify y/a * a = y, then use commutativity
  have h_cancel : ∀ y : RPos, y / a * a = y := fun y => by
    ext; simp [RPos.div_val, div_mul_cancel₀ _ a.2.ne']
  simp_rw [rpDivEquiv_apply, h_cancel]
  congr 1; ext y; exact mul_comm (G := ℂ) _ _

/-- **Lemma 1, Part 3**: `f(a) + f(a⁻¹) = 2 Re⟨g, U_a g⟩`.

    Reference: lamportform.tex, Step 3, first part (lines 158–160).

    Proof: Direct from Parts 1 and 2: `z + conj(z) = 2 Re(z)`. -/
theorem convolution_add_inv (g : RPos → ℂ) (a : RPos)
    (hg : MemLp g 2 haarMult) :
    mulConv g (mulInvol g) a + mulConv g (mulInvol g) a⁻¹ =
    2 * ↑(re (mulConv g (mulInvol g) a)) := by
  rw [convolution_inv_eq_conj g a hg]
  simp [re_eq_add_conj]
  ring

/-- **Lemma 1, Part 4**: `f(1) = ‖g‖²`.

    Reference: lamportform.tex, Step 3, second part (line 160).

    Proof: At `a = 1`, `U_1 = id`, so `⟨g, U_1 g⟩ = ⟨g, g⟩ = ‖g‖²`. -/
theorem convolution_at_one (g : RPos → ℂ) (hg : MemLp g 2 haarMult) :
    mulConv g (mulInvol g) 1 =
    ↑(∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂haarMult).toReal := by
  -- Step 1: Unfold convolution at a=1
  rw [mulConv_mulInvol_apply]
  -- Step 2: Simplify y / 1 = y
  simp_rw [show ∀ y : RPos, y / 1 = y from fun y => Subtype.ext (div_one y.val)]
  -- Step 3: z * conj(z) = ‖z‖² for complex numbers
  simp_rw [RCLike.mul_conj]
  -- Goal: ∫ y, ↑‖g y‖ ^ 2 ∂haarMult = ↑(∫⁻ x, ↑‖g x‖₊ ^ (2:ℝ) ∂haarMult).toReal
  -- Step 4: Normalize casts — pulls ↑ out of integral via integral_ofReal
  norm_cast
  -- Step 5: Strip ↑ from both sides
  congr 1
  -- Step 6: Convert Bochner integral to lintegral for nonneg function
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (hg.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable]
  -- Step 7: Pointwise ENNReal conversion inside lintegral
  congr 1
  apply lintegral_congr
  intro x
  have h_two : (2 : ℝ) = ((2 : ℕ) : ℝ) := by simp
  rw [← Real.rpow_natCast _ 2, ← h_two,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, ofReal_norm_eq_enorm]
  norm_cast

end

end ConnesLean
