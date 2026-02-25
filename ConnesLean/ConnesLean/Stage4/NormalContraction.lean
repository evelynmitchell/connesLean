/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Normal Contractions and Real-to-Complex Bridge

Reference: lamportform.tex, Section 5, lines 476–479.

A normal contraction is a map `Φ : ℝ → ℝ` satisfying `Φ(0) = 0` and
`|Φ(a) - Φ(b)| ≤ |a - b|` for all `a, b`.

This file defines normal contractions, the `liftReal` embedding `ℝ → ℂ`,
and bridge lemmas connecting real-valued indicators to the ℂ-typed
`zeroExtend`/`energyForm` API.
-/

import ConnesLean.Stage2.LogCoordinates

namespace ConnesLean

open MeasureTheory Real Set

noncomputable section

/-! ## Normal contractions -/

/-- A normal contraction is a map `Φ : ℝ → ℝ` with `Φ(0) = 0` and
    `|Φ(a) - Φ(b)| ≤ |a - b|` for all `a, b` (i.e., 1-Lipschitz).

    Reference: lamportform.tex, lines 476–479. -/
structure IsNormalContraction (Φ : ℝ → ℝ) : Prop where
  map_zero : Φ 0 = 0
  lipschitz : LipschitzWith 1 Φ

/-! ## Basic instances -/

/-- The absolute value function `|·|` is a normal contraction.
    Uses the reverse triangle inequality `||a| - |b|| ≤ |a - b|`. -/
theorem isNormalContraction_abs : IsNormalContraction (fun x => |x|) where
  map_zero := abs_zero
  lipschitz := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    exact abs_abs_sub_abs_le_abs_sub x y

/-- The identity function is a normal contraction. -/
theorem isNormalContraction_id : IsNormalContraction id where
  map_zero := rfl
  lipschitz := LipschitzWith.id

/-! ## Properties of normal contractions -/

/-- A normal contraction is bounded by the identity: `|Φ(a)| ≤ |a|`.
    Set `b = 0` in the Lipschitz condition and use `Φ(0) = 0`. -/
theorem IsNormalContraction.bound (hΦ : IsNormalContraction Φ) (a : ℝ) :
    |Φ a| ≤ |a| := by
  have h := hΦ.lipschitz.dist_le_mul a 0
  simp only [hΦ.map_zero, NNReal.coe_one, one_mul, dist_zero_right] at h
  exact h

/-- A normal contraction is measurable (Lipschitz → continuous → measurable). -/
theorem IsNormalContraction.measurable (hΦ : IsNormalContraction Φ) :
    Measurable Φ :=
  hΦ.lipschitz.continuous.measurable

/-! ## Indicator composition -/

/-- Composing an indicator with a zero-preserving function commutes:
    `I.indicator (Φ ∘ G) = Φ ∘ (I.indicator G)` when `Φ(0) = 0`.

    This is a direct application of `Set.indicator_comp_of_zero`. -/
theorem indicator_comp_normalContraction (hΦ : IsNormalContraction Φ)
    (G : ℝ → ℝ) (I : Set ℝ) :
    I.indicator (Φ ∘ G) = Φ ∘ (I.indicator G) :=
  Set.indicator_comp_of_zero hΦ.map_zero

/-! ## The liftReal embedding -/

/-- Embed a real-valued function into `ℝ → ℂ` via the canonical coercion.
    This is used to feed real-valued functions into the ℂ-typed energy form. -/
def liftReal (G : ℝ → ℝ) : ℝ → ℂ := fun u => ↑(G u)

@[simp]
theorem liftReal_apply (G : ℝ → ℝ) (u : ℝ) : liftReal G u = ↑(G u) := rfl

/-! ## Bridge lemmas: zeroExtend ↔ liftReal -/

/-- Zero-extending a lifted real function factors through the real indicator:
    `zeroExtend (liftReal G) I u = ↑(I.indicator G u)`.

    Uses `Set.indicator_comp_of_zero` with `Complex.ofReal_zero`. -/
theorem zeroExtend_liftReal (G : ℝ → ℝ) (I : Set ℝ) :
    zeroExtend (liftReal G) I = fun u => ↑(I.indicator G u) :=
  Set.indicator_comp_of_zero Complex.ofReal_zero

/-- Key bridge lemma: zero-extending a lifted composition factors through
    the real indicator composed with Φ:
    `zeroExtend (liftReal (Φ ∘ G)) I = fun u => ↑(Φ (I.indicator G u))`.

    This is the critical connection between `zeroExtend` (typed `ℝ → ℂ`)
    and the real-valued indicator needed for Lipschitz bounds in PR B.

    Proof: two applications of `Set.indicator_comp_of_zero` — first for `Φ`
    (via `hΦ.map_zero`), then for `(↑· : ℝ → ℂ)` (via `Complex.ofReal_zero`). -/
theorem zeroExtend_liftReal_comp (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ)
    (I : Set ℝ) :
    zeroExtend (liftReal (Φ ∘ G)) I = fun u => ↑(Φ (I.indicator G u)) := by
  unfold zeroExtend liftReal
  have h1 : I.indicator (Φ ∘ G) = Φ ∘ I.indicator G :=
    Set.indicator_comp_of_zero hΦ.map_zero
  have h2 : I.indicator ((↑· : ℝ → ℂ) ∘ (Φ ∘ G)) =
      (↑·) ∘ I.indicator (Φ ∘ G) :=
    Set.indicator_comp_of_zero Complex.ofReal_zero
  rw [h1] at h2
  convert h2 using 1

/-! ## Norm bridge lemmas -/

/-- Subtraction commutes with `liftReal`:
    `liftReal a u - liftReal b u = ↑(a u - b u)`. -/
theorem liftReal_sub_apply (a b : ℝ → ℝ) (u : ℝ) :
    liftReal a u - liftReal b u = ↑(a u - b u) := by
  simp [liftReal, Complex.ofReal_sub]

/-- The nnnorm bridge: `‖liftReal a u - liftReal b u‖₊ = ‖a u - b u‖₊`.
    Reduces ℂ-valued nnnorm to ℝ-valued nnnorm via
    `Complex.ofReal_sub` and `Complex.nnnorm_real`. -/
theorem nnnorm_liftReal_sub (a b : ℝ → ℝ) (u : ℝ) :
    ‖liftReal a u - liftReal b u‖₊ = ‖a u - b u‖₊ := by
  rw [liftReal_sub_apply, Complex.nnnorm_real]

/-! ## Pointwise norm inequality under contraction -/

/-- Pointwise nnnorm inequality: applying a normal contraction decreases nnnorms.
    `‖↑(Φ a) - ↑(Φ b)‖₊ ≤ ‖↑a - ↑b‖₊` in ℂ.

    This is the key ingredient for `lintegral_mono` in the Markov property. -/
theorem nnnorm_comp_le (hΦ : IsNormalContraction Φ) (a b : ℝ) :
    ‖(↑(Φ a) : ℂ) - ↑(Φ b)‖₊ ≤ ‖(↑a : ℂ) - ↑b‖₊ := by
  rw [← Complex.ofReal_sub, Complex.nnnorm_real,
      ← Complex.ofReal_sub, Complex.nnnorm_real]
  have h := hΦ.lipschitz.dist_le_mul a b
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  exact_mod_cast h

end

end ConnesLean
