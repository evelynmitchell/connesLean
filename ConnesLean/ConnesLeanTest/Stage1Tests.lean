/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 1 Property Tests

Verification tests for Stage 1 definitions and theorems.
-/

import ConnesLean

open ConnesLean

noncomputable section

/-! ## RPos tests -/

/-- Test that `RPos.One` has value 1. -/
example : (1 : RPos).val = 1 := rfl

/-- Test that multiplication of positive reals has the right value. -/
example : ((⟨2, by norm_num⟩ : RPos) * ⟨3, by norm_num⟩).val = 6 := by
  simp [RPos.mul_val]; norm_num

/-- Test that inversion of positive reals has the right value. -/
example : ((⟨2, by norm_num⟩ : RPos)⁻¹).val = (2 : ℝ)⁻¹ := rfl

/-! ## Dilation operator tests -/

/-- Test that dilation at 1 is the identity. -/
example (g : RPos → ℂ) : dilationOp 1 g = g := dilationOp_one g

/-- Test that `U_{a⁻¹} ∘ U_a = id`. -/
example (a : RPos) (g : RPos → ℂ) : dilationOp a⁻¹ (dilationOp a g) = g :=
  dilationOp_inv a g

/-! ## Involution tests -/

/-- Test that involution is involutive: `(g*)* = g`. -/
example (g : RPos → ℂ) : mulInvol (mulInvol g) = g :=
  mulInvol_involutive g

/-! ## Convolution tests -/

/-- Test that `mulConv g (mulInvol g)` expands to `∫ g(y) * conj(g(y/a)) d*y`. -/
example (g : RPos → ℂ) (a : RPos) :
    mulConv g (mulInvol g) a =
    ∫ y, g y * starRingEnd ℂ (g (y / a)) ∂haarMult :=
  mulConv_mulInvol_apply g a

/-- Test that the convolution integrand is integrable for `g ∈ L²(d*x)`. -/
example (g : RPos → ℂ) (hg : MeasureTheory.MemLp g 2 haarMult) (a : RPos) :
    MeasureTheory.Integrable (fun y => g y * starRingEnd ℂ (g (y / a))) haarMult :=
  mulConv_mulInvol_integrable g hg a

/-- Test that `(g ⋆ g*)(a) = ⟨g, U_a g⟩`. -/
example (g : RPos → ℂ) (a : RPos) :
    mulConv g (mulInvol g) a =
    ∫ y, g y * starRingEnd ℂ (dilationOp a g y) ∂haarMult :=
  convolution_eq_inner g a

/-- Test that `f(1) = ‖g‖²`. -/
example (g : RPos → ℂ) (hg : MeasureTheory.MemLp g 2 haarMult) :
    mulConv g (mulInvol g) 1 =
    ↑(∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂haarMult).toReal :=
  convolution_at_one g hg

/-! ## Unitary identity tests -/

/-- Test the unitary identity corollary for the identity (trivial case):
    `2 Re⟨h, h⟩ = 2‖h‖²`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (h : E) : 2 * RCLike.re (@inner ℂ E _ h h) = 2 * ‖h‖ ^ 2 :=
  unitary_identity_id h

end
