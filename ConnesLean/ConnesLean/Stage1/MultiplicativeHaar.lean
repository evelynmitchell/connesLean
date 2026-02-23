/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multiplicative Haar Measure on R_+*

Reference: lamportform.tex, Section 1, lines 94–101.

We define the multiplicative Haar measure `d*x = dx/x` on `R_+* = (0, ∞)` as the
pushforward of Lebesgue measure on `ℝ` under the exponential map `exp : ℝ → R_+*`.
This automatically gives the correct measure because for `f : R_+* → ℝ`:
  `∫ f(x) d(map exp vol)(x) = ∫ f(exp u) du`
and setting `x = exp u`, `dx = exp(u) du`, so `du = dx/x = d*x`.

## Inner product convention
See `ConnesLean.Common.Notation` for the convention on inner products.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ConnesLean

open MeasureTheory Real Set Filter

noncomputable section

/-! ## The type of positive reals -/

/-- The type of positive reals `R_+* = (0, ∞)`, the multiplicative group underlying
    the Haar measure `d*x = dx/x`. We use a subtype of `ℝ` for compatibility with
    Mathlib's measure theory and analysis libraries. -/
abbrev RPos := {x : ℝ // 0 < x}

namespace RPos

instance : One RPos := ⟨⟨1, one_pos⟩⟩

instance : Mul RPos := ⟨fun a b => ⟨a.val * b.val, mul_pos a.property b.property⟩⟩

instance : Inv RPos := ⟨fun a => ⟨a.val⁻¹, inv_pos.mpr a.property⟩⟩

instance : Div RPos := ⟨fun a b => ⟨a.val / b.val, div_pos a.property b.property⟩⟩

/-- The inclusion of `RPos` into `ℝ`. -/
def toReal (x : RPos) : ℝ := x.val

@[simp] theorem toReal_pos (x : RPos) : 0 < x.val := x.property

@[simp] theorem toReal_ne_zero (x : RPos) : x.val ≠ 0 := ne_of_gt x.property

@[simp] theorem one_val : (1 : RPos).val = 1 := rfl

@[simp] theorem mul_val (a b : RPos) : (a * b).val = a.val * b.val := rfl

@[simp] theorem inv_val (a : RPos) : (a⁻¹).val = a.val⁻¹ := rfl

@[simp] theorem div_val (a b : RPos) : (a / b).val = a.val / b.val := rfl

instance : TopologicalSpace RPos := instTopologicalSpaceSubtype

instance : MeasurableSpace RPos := Subtype.instMeasurableSpace

end RPos

/-! ## Exponential and logarithmic maps -/

/-- The exponential map from `ℝ` to `RPos`, serving as the logarithmic coordinate change.
    This is the key isomorphism: `(ℝ, +, dx) ≅ (R_+*, ×, d*x)`. -/
def expToRPos (u : ℝ) : RPos := ⟨exp u, exp_pos u⟩

/-- The logarithmic map from `RPos` to `ℝ`, inverse of `expToRPos`. -/
def logFromRPos (x : RPos) : ℝ := log x.val

@[simp]
theorem logFromRPos_expToRPos (u : ℝ) : logFromRPos (expToRPos u) = u := by
  simp [logFromRPos, expToRPos, log_exp]

@[simp]
theorem expToRPos_logFromRPos (x : RPos) : expToRPos (logFromRPos x) = x := by
  ext
  simp [logFromRPos, expToRPos, exp_log x.property]

/-- Measurability of the exponential map to `RPos`. -/
theorem measurable_expToRPos : Measurable expToRPos := by
  sorry

/-- Measurability of the logarithmic map from `RPos`. -/
theorem measurable_logFromRPos : Measurable logFromRPos := by
  sorry

/-! ## The multiplicative Haar measure -/

/-- The multiplicative Haar measure on `R_+*`, defined as the pushforward of
    Lebesgue measure under `exp`. This gives `d*x = dx/x` because:
    `∫ f(x) d(map exp vol)(x) = ∫ f(exp u) du`, and `du = dx/x`. -/
def haarMult : Measure RPos :=
  Measure.map expToRPos volume

/-- The multiplicative Haar measure is sigma-finite, inherited from
    the sigma-finiteness of Lebesgue measure on `ℝ`. -/
instance haarMult_sigmaFinite : SigmaFinite haarMult := by
  sorry

/-- Left-invariance of the Haar measure under multiplication: for any `a ∈ R_+*`
    and measurable `S ⊆ R_+*`, `μ(a · S) = μ(S)`.

    Reference: lamportform.tex, Section 1, line 99: `d*(x/a) = d*x`. -/
theorem haarMult_mul_invariant (a : RPos) (S : Set RPos) (hS : MeasurableSet S) :
    haarMult ((fun x => a * x) '' S) = haarMult S := by
  sorry

end

end ConnesLean
