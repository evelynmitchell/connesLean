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
    (hg : MemLp g 2 haarMult) :
    mulConv g (mulInvol g) a⁻¹ = starRingEnd ℂ (mulConv g (mulInvol g) a) := by
  sorry

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
  sorry

end

end ConnesLean
