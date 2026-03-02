/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 8 Property Tests

Verification tests for Stage 8 definitions and theorems covering
inversion symmetry and the even ground state.
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real Filter

noncomputable section

/-! ## Reflection operator tests -/

/-- reflectionOp is an involution. -/
example (φ : ℝ → ℂ) : reflectionOp (reflectionOp φ) = φ :=
  reflectionOp_reflectionOp φ

/-- reflectionOp_apply unfolds correctly. -/
example (φ : ℝ → ℂ) (u : ℝ) : reflectionOp φ u = φ (-u) :=
  reflectionOp_apply φ u

/-- logInterval is symmetric under negation. -/
example (L x : ℝ) (hx : x ∈ logInterval L) : -x ∈ logInterval L :=
  logInterval_neg_mem hx

/-! ## Even ground state tests -/

/-- ground_state_even composes correctly. -/
example (Λ : ℝ) (hΛ : 1 < Λ) :
    reflectionOp (ground_state_exists Λ hΛ).eigenfunction
      =ᵐ[volume] (ground_state_exists Λ hΛ).eigenfunction :=
  ground_state_even Λ hΛ

/-- resolvent_commutes_reflection has the right type signature. -/
example (Λ : ℝ) (hΛ : 1 < Λ) (φ : ℝ → ℂ) :
    ∀ᵐ x ∂volume,
      (kato_operator Λ hΛ).resolvent (reflectionOp φ) x =
      reflectionOp ((kato_operator Λ hΛ).resolvent φ) x :=
  resolvent_commutes_reflection Λ hΛ φ

end
