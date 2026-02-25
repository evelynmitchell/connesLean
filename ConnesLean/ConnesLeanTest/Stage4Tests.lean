/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 4 Property Tests

Verification tests for Stage 4 definitions and theorems covering
normal contractions and the real-to-complex bridge.
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real

noncomputable section

/-! ## IsNormalContraction tests -/

/-- Absolute value is a normal contraction. -/
example : IsNormalContraction (fun x => |x|) :=
  isNormalContraction_abs

/-- The identity is a normal contraction. -/
example : IsNormalContraction id :=
  isNormalContraction_id

/-- Normal contractions are bounded: |Φ(a)| ≤ |a|. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (a : ℝ) :
    |Φ a| ≤ |a| :=
  hΦ.bound a

/-- Normal contractions are measurable. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) : Measurable Φ :=
  hΦ.measurable

/-! ## Indicator composition tests -/

/-- Indicator commutes with normal contraction composition. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (I : Set ℝ) :
    I.indicator (Φ ∘ G) = Φ ∘ (I.indicator G) :=
  indicator_comp_normalContraction hΦ G I

/-! ## liftReal tests -/

/-- liftReal applies correctly: casts to ℂ. -/
example (G : ℝ → ℝ) (u : ℝ) : liftReal G u = ↑(G u) :=
  liftReal_apply G u

/-! ## Bridge lemma tests -/

/-- zeroExtend of liftReal factors through indicator. -/
example (G : ℝ → ℝ) (I : Set ℝ) :
    zeroExtend (liftReal G) I = fun u => ↑(I.indicator G u) :=
  zeroExtend_liftReal G I

/-- zeroExtend of liftReal composed with contraction factors correctly. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (I : Set ℝ) :
    zeroExtend (liftReal (Φ ∘ G)) I = fun u => ↑(Φ (I.indicator G u)) :=
  zeroExtend_liftReal_comp hΦ G I

/-! ## Norm bridge tests -/

/-- Subtraction commutes with liftReal. -/
example (a b : ℝ → ℝ) (u : ℝ) :
    liftReal a u - liftReal b u = ↑(a u - b u) :=
  liftReal_sub_apply a b u

/-- nnnorm bridge: ℂ nnnorm = ℝ nnnorm for lifted functions. -/
example (a b : ℝ → ℝ) (u : ℝ) :
    ‖liftReal a u - liftReal b u‖₊ = ‖a u - b u‖₊ :=
  nnnorm_liftReal_sub a b u

/-- Pointwise nnnorm decrease under normal contraction. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (a b : ℝ) :
    ‖(↑(Φ a) : ℂ) - ↑(Φ b)‖₊ ≤ ‖(↑a : ℂ) - ↑b‖₊ :=
  nnnorm_comp_le hΦ a b

end
