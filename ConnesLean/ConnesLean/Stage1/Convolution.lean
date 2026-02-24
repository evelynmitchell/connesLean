/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multiplicative Convolution and Involution on R_+*

Reference: lamportform.tex, Section 1, lines 102-109.

Multiplicative convolution: (g * h)(x) = integral g(y) h(x/y) d*y
Involution: g*(x) = conj(g(x^{-1}))

## Inner product convention
See `ConnesLean.Common.Notation` for the convention on inner products.
-/

import ConnesLean.Stage1.MultiplicativeHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

namespace ConnesLean

open MeasureTheory Complex

noncomputable section

/-- Multiplicative convolution of two functions on `R_+*`:
    `(mulConv g h)(x) = integral g(y) * h(x/y) d*y`.

    We define this as a plain function `RPos -> C`, not as an `Lp` element,
    to allow pointwise evaluation (needed for Lemma 1).

    Reference: lamportform.tex, lines 102-105. -/
def mulConv (g h : RPos -> ℂ) : RPos -> ℂ :=
  fun x => ∫ y, g y * h (x / y) ∂haarMult

/-- The involution `g* : R_+* -> C` defined by `g*(x) = conj(g(x^{-1}))`.

    Reference: lamportform.tex, lines 106-109. -/
def mulInvol (g : RPos -> ℂ) : RPos -> ℂ :=
  fun x => starRingEnd ℂ (g x⁻¹)

/-- `mulInvol` is involutive: `(g*)* = g`. -/
theorem mulInvol_involutive : Function.Involutive mulInvol := by
  intro g; ext x; simp only [mulInvol]
  -- Goal: (starRingEnd ℂ) ((starRingEnd ℂ) (g x⁻¹⁻¹)) = g x
  -- starRingEnd ℂ is definitionally star (= Complex.conj)
  change star (star (g x⁻¹⁻¹)) = g x
  rw [star_star]
  congr 1; ext; simp [RPos.inv_val, inv_inv]

/-- Applying involution twice returns the original function. -/
@[simp]
theorem mulInvol_mulInvol (g : RPos -> ℂ) :
    mulInvol (mulInvol g) = g :=
  mulInvol_involutive g

/-- Expand `(mulConv g (mulInvol g))(a)` to `integral g(y) * conj(g(y/a)) d*y`.

    Reference: lamportform.tex, Lemma 1.1, Steps 1.1-1.3.

    The key computation uses `(a/y)^{-1} = y/a`. -/
theorem mulConv_mulInvol_apply (g : RPos -> ℂ) (a : RPos) :
    mulConv g (mulInvol g) a =
    ∫ y, g y * starRingEnd ℂ (g (y / a)) ∂haarMult := by
  unfold mulConv mulInvol
  congr 1; ext y
  -- Goal: g y * (starRingEnd ℂ) (g (a / y)⁻¹) = g y * (starRingEnd ℂ) (g (y / a))
  -- Suffices to show (a / y)⁻¹ = y / a as RPos elements
  have h : (a / y)⁻¹ = y / a := by
    ext; simp [RPos.div_val, RPos.inv_val, inv_div]
  rw [h]

/-- The integrand of `mulConv g (mulInvol g)` is integrable for `g ∈ L²(d*x)`.
    Follows from Hölder's inequality applied to `g` and `star(g ∘ (· / a))`,
    both in `L²(d*x)`, using measure-preservation of `(· / a)`. -/
theorem mulConv_mulInvol_integrable (g : RPos → ℂ)
    (hg : MemLp g 2 haarMult) (a : RPos) :
    Integrable (fun y => g y * starRingEnd ℂ (g (y / a))) haarMult := by
  -- Step 1: Division by `a` is measure-preserving on (RPos, haarMult)
  have h_mp : MeasurePreserving (rpDivEquiv a) haarMult haarMult :=
    measurePreserving_rpDiv a
  -- Step 2: g ∘ (· / a) ∈ L², hence star(g ∘ (· / a)) ∈ L²
  have h_conj : MemLp (star (g ∘ (· / a))) 2 haarMult :=
    (hg.comp_measurePreserving h_mp).star
  -- Step 3: Hölder (L² × L² → L¹)
  exact hg.integrable_mul h_conj

end

end ConnesLean
