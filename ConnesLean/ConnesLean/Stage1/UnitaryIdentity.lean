/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma 2: A Basic Unitary Identity

Reference: lamportform.tex, Lemma 1.2 (`lem:unitary`), lines 166–191.

For any unitary (isometric) operator `U` on a Hilbert space and any vector `h`:
  `2 Re⟨h, Uh⟩ = 2‖h‖² - ‖h - Uh‖²`

This is stated generically for an abstract inner product space and a
linear isometry, independent of the multiplicative setup.

## Proof structure (4 steps, all elementary algebra)
1. Expand `‖h - Uh‖² = ‖h‖² + ‖Uh‖² - 2 Re⟨h, Uh⟩`   (via `norm_sub_sq`)
2. Use isometry: `‖Uh‖² = ‖h‖²`
3. Substitute: `‖h - Uh‖² = 2‖h‖² - 2 Re⟨h, Uh⟩`
4. Rearrange
-/

import Mathlib.Analysis.InnerProductSpace.Basic

namespace ConnesLean

open RCLike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Lemma 2** (Basic unitary identity): For any linear isometry `U` on a
    Hilbert space and any vector `h`,
    `2 Re⟨h, Uh⟩ = 2‖h‖² - ‖h - Uh‖²`.

    Reference: lamportform.tex, Lemma 1.2, lines 166–191.

    Note: We state this for a `LinearIsometry`, which captures the isometric
    property `‖Uh‖ = ‖h‖` used in Step 2 of the proof. Unitarity (surjectivity)
    is not needed for this identity. -/
theorem unitary_identity (U : E →ₗᵢ[ℂ] E) (h : E) :
    2 * re (@inner ℂ E _ h (U h)) = 2 * ‖h‖ ^ 2 - ‖h - U h‖ ^ 2 := by
  -- Step 1: Expand ‖h - Uh‖² using norm_sub_sq (works for any RCLike field)
  -- norm_sub_sq : ‖x - y‖² = ‖x‖² - 2 * re ⟪x, y⟫ + ‖y‖²
  have step1 := norm_sub_sq (𝕜 := ℂ) h (U h)
  -- step1 : ‖h - U h‖² = ‖h‖² - 2 * re ⟪h, U h⟫_ℂ + ‖U h‖²
  -- Step 2: ‖Uh‖ = ‖h‖ by isometry
  have step2 : ‖U h‖ = ‖h‖ := U.norm_map h
  -- Step 2': square both sides for linarith
  have step2_sq : ‖U h‖ ^ 2 = ‖h‖ ^ 2 := by rw [step2]
  -- Steps 3–4: Substitute and rearrange (all linear in the squared norms)
  linarith

/-- Variant of the unitary identity using `LinearIsometryEquiv`
    (i.e., a truly unitary operator). -/
theorem unitary_identity' (U : E ≃ₗᵢ[ℂ] E) (h : E) :
    2 * re (@inner ℂ E _ h (U h)) = 2 * ‖h‖ ^ 2 - ‖h - U h‖ ^ 2 :=
  unitary_identity U.toLinearIsometry h

/-- Corollary: When `U = id`, we get `2 Re⟨h, h⟩ = 2‖h‖²`.

    Proof: `re ⟪h, h⟫ = ‖h‖²` by `inner_self_eq_norm_sq`. -/
theorem unitary_identity_id (h : E) :
    2 * re (@inner ℂ E _ h h) = 2 * ‖h‖ ^ 2 := by
  have := inner_self_eq_norm_sq (𝕜 := ℂ) (x := h)
  -- this : re ⟪h, h⟫_ℂ = ‖h‖ ^ 2
  linarith

end ConnesLean
