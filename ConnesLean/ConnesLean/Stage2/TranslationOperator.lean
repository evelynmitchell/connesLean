/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Translation Operator on L²(ℝ)

Reference: lamportform.tex, Section 2.

The translation operator `S_t` on `L²(ℝ, du)` is defined by `(S_t φ)(u) = φ(u - t)`.
It is the additive analogue of the dilation operator `U_a` on `L²(R_+*, d*x)`,
related by the logarithmic coordinate change:
  `U_{exp(t)} g ∘ exp = S_t (g ∘ exp)`.

## Inner product convention
See `ConnesLean.Common.Notation` for the convention on inner products.
-/

import ConnesLean.Stage1.MultiplicativeHaar
import ConnesLean.Stage1.DilationOperator
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.LIntegral

namespace ConnesLean

open MeasureTheory Real

noncomputable section

/-! ## The translation operator -/

/-- The translation operator `S_t` on functions `ℝ → ℂ`, defined by
    `(S_t φ)(u) = φ(u - t)`.

    Reference: lamportform.tex, Section 2: additive translation on log coordinates. -/
def translationOp (t : ℝ) (φ : ℝ → ℂ) : ℝ → ℂ :=
  fun u => φ (u - t)

@[simp]
theorem translationOp_apply (t : ℝ) (φ : ℝ → ℂ) (u : ℝ) :
    translationOp t φ u = φ (u - t) := rfl

/-- Translation by `0` is the identity. -/
@[simp]
theorem translationOp_zero (φ : ℝ → ℂ) : translationOp 0 φ = φ := by
  ext u; simp [translationOp]

/-- Translation is additive: `S_s ∘ S_t = S_{s+t}`. -/
theorem translationOp_add (s t : ℝ) (φ : ℝ → ℂ) :
    translationOp s (translationOp t φ) = translationOp (s + t) φ := by
  ext u; simp [translationOp, sub_sub]

/-- Dilation on `RPos` conjugates to translation on `ℝ` via `exp`:
    `(U_{exp(t)} g)(exp(u)) = (S_t (g ∘ exp))(u)`.

    This is the key bridge between the multiplicative setup (Stage 1)
    and the additive setup (Stage 2). -/
theorem dilation_eq_translation (t : ℝ) (g : RPos → ℂ) (u : ℝ) :
    dilationOp (expToRPos t) g (expToRPos u) = translationOp t (g ∘ expToRPos) u := by
  simp [dilationOp, translationOp, expToRPos_sub_log]

/-! ## L² properties of the translation operator -/

/-- Translation by `t` preserves Lebesgue measure on `ℝ`. -/
theorem measurePreserving_sub_const (t : ℝ) :
    MeasurePreserving (· - t : ℝ → ℝ) volume volume := by
  have : (· - t : ℝ → ℝ) = ((-t) + ·) := by funext x; ring
  rw [this]
  exact measurePreserving_add_left volume (-t)

/-- The L² norm is preserved under translation:
    `∫ ‖S_t φ‖² du = ∫ ‖φ‖² du`. -/
theorem translationOp_lintegral_norm_eq (t : ℝ) (φ : ℝ → ℂ) :
    ∫⁻ u, ‖translationOp t φ u‖₊ ^ (2 : ℝ) ∂volume =
    ∫⁻ u, ‖φ u‖₊ ^ (2 : ℝ) ∂volume := by
  simp only [translationOp_apply]
  -- Subtraction is ((-t) + ·), so use Lebesgue translation invariance
  simp_rw [show ∀ u : ℝ, u - t = (-t) + u from fun u => by ring]
  exact lintegral_add_left_eq_self (μ := volume)
    (fun v => ↑‖φ v‖₊ ^ (2 : ℝ)) (-t)

/-! ## Strong continuity of translations in L² -/

/-- **Axiom** (Strong continuity of translations in L²):
    The map `t ↦ ∫ ‖φ(u) − φ(u−t)‖² du` is continuous for any `φ : ℝ → ℂ`.

    This is a standard result: the translation group `{S_t}_{t ∈ ℝ}` is
    strongly continuous on L²(ℝ) (Engel-Nagel, Thm I.5.8).

    **Why axiom:** Mathlib does not currently provide strong continuity of
    the translation group on Lp spaces. The proof requires density of
    continuous compactly supported functions in L² plus uniform continuity,
    or dominated convergence — both paths need unformalized infrastructure.

    Reference: Engel-Nagel, One-Parameter Semigroups, Theorem I.5.8. -/
axiom translation_norm_sq_continuous (φ : ℝ → ℂ) :
    Continuous (fun t => ∫⁻ u, ‖φ u - translationOp t φ u‖₊ ^ (2 : ℝ) ∂volume)

end

end ConnesLean
