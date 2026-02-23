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
    (hg : MemLp g 2 haarMult) :
    ∫⁻ x, ‖dilationOp a g x‖₊ ^ (2 : ℝ) ∂haarMult =
    ∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂haarMult := by
  sorry

/-- The Cauchy-Schwarz bound: |<g, U_a g>| <= ||g||_2^2.

    Reference: lamportform.tex, line 118-119:
    |<g, U_a g>| <= ||g||_2 * ||U_a g||_2 = ||g||_2^2. -/
theorem inner_dilationOp_le (a : RPos) (g : RPos -> ℂ)
    (hg : MemLp g 2 haarMult) :
    ‖∫ x, g x * starRingEnd ℂ (dilationOp a g x) ∂haarMult‖ ≤
    (∫⁻ x, ‖g x‖₊ ^ (2 : ℝ) ∂haarMult).toReal := by
  sorry

end

end ConnesLean
