/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 7 Property Tests

Verification tests for Stage 7 definitions and theorems covering
the positivity-improving semigroup and ground state existence.
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real Filter

noncomputable section

/-! ## Positivity improving tests -/

/-- IsPositivityImproving composes with axiom 1. -/
example (Λ : ℝ) (hΛ : 1 < Λ) :
    IsPositivityImproving Λ (kato_operator Λ hΛ) :=
  semigroup_positivity_improving Λ hΛ

/-! ## Ground state tests -/

/-- ground_state_exists composes correctly. -/
example (Λ : ℝ) (hΛ : 1 < Λ) :
    GroundState Λ (kato_operator Λ hΛ) :=
  ground_state_exists Λ hΛ

/-- Eigenvalue is nonneg. -/
example (Λ : ℝ) (hΛ : 1 < Λ) :
    0 ≤ (ground_state_exists Λ hΛ).eigenvalue :=
  (ground_state_exists Λ hΛ).eigenvalue_nonneg

/-- Eigenfunction is in the form domain. -/
example (Λ : ℝ) (hΛ : 1 < Λ) :
    (ground_state_exists Λ hΛ).eigenfunction ∈ formDomain Λ :=
  (ground_state_exists Λ hΛ).eigenfunction_in_domain

/-- Eigenfunction is nonzero. -/
example (Λ : ℝ) (hΛ : 1 < Λ) :
    ∃ x, (ground_state_exists Λ hΛ).eigenfunction x ≠ 0 :=
  (ground_state_exists Λ hΛ).eigenfunction_nonzero

end
