/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Axiom Soundness Tests

Executable cross-checks that verify axiom conclusions at degenerate inputs
are consistent with independently proven facts. These catch overpowered
axioms (cf. PR #91) by testing that axiom outputs agree with base cases
we can compute without the axiom.

Three categories:
1. **Cross-axiom consistency**: axiom + proved fact → no contradiction
2. **Degenerate-input extraction**: axiom applied to zero/empty → consistent
3. **Non-vacuity**: axiom hypotheses are satisfiable
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real Filter

noncomputable section

/-! ## 1. Cross-axiom consistency at G = 0

The Fourier representation axiom says E_λ(G) = (1/2π) ∫ ψ_λ(ξ)|Ĝ(ξ)|² dξ.
We know E_λ(0) = 0 (proved in Stage 2 without any axioms).
Cross-check: the Fourier integral at G=0 must also be 0. -/

/-- Fourier representation applied to the zero function: the Fourier integral
    equals (energyForm Λ 0).toReal, which we independently know is 0. -/
example (Λ : ℝ) (hLam : 1 < Λ) :
    (1 / (2 * Real.pi)) *
    ∫ ξ, fourierSymbol Λ ξ * ‖FourierTransform.fourier (0 : ℝ → ℂ) ξ‖ ^ 2 = 0 := by
  rw [← energyForm_eq_fourierSymbol_integral Λ hLam 0 (zero_mem_formDomain Λ)]
  simp [energyForm_zero]

/-! ## 2. Form domain biconditional at G = 0

The formDomain_eq_weighted_fourier axiom gives G ∈ D(E_λ) ↔ (Fourier conditions).
We prove 0 ∈ D(E_λ) without axioms (via energyForm_zero), so the forward
direction extracts the Fourier conditions for G=0. -/

/-- Extracting Fourier conditions for the zero function from the domain axiom.
    The forward direction of the biconditional must be satisfiable at G=0. -/
example (Λ : ℝ) (hLam : 1 < Λ) :
    (∫⁻ ξ, ↑‖FourierTransform.fourier (0 : ℝ → ℂ) ξ‖₊ ^ 2 < ⊤ ∧
     ∫⁻ ξ, ↑(fourierSymbol Λ ξ).toNNReal *
       ↑‖FourierTransform.fourier (0 : ℝ → ℂ) ξ‖₊ ^ 2 < ⊤) :=
  (formDomain_eq_weighted_fourier Λ hLam 0).mp (zero_mem_formDomain Λ)

/-! ## 3. Closedness axiom: zero_energy field consistency

The closedness axiom provides a structure with a `zero_energy` field
proving E_λ(0) = 0. This must be consistent with the independently
proved `energyForm_zero`. -/

/-- The closedness axiom's zero_energy field and the proved energyForm_zero
    both witness the same statement — extract and verify both exist. -/
example (Λ : ℝ) (hLam : 1 < Λ) :
    (energyForm_closed_on_line Λ hLam).zero_energy = energyForm_zero Λ :=
  rfl  -- Lean 4 proof irrelevance is definitional: any two proofs of the same Prop are rfl-equal

/-! ## 4. Kato resolvent at f = 0

The form identity says ‖R(f)‖₂² + E_λ(R(f)) ≤ ‖f‖₂² for all f.
At f = 0, the RHS is 0 (ENNReal). Since both LHS summands are nonneg,
both must be 0. This means the resolvent of zero has zero energy. -/

/-- Form identity at f=0: the resolvent of zero has zero energy. -/
example (Λ : ℝ) (hLam : 1 < Λ) :
    energyForm Λ ((kato_operator Λ hLam).resolvent 0) = 0 := by
  have h := (kato_operator Λ hLam).form_identity 0
  have h_rhs : (∫⁻ u, ‖(0 : ℝ → ℂ) u‖₊ ^ (2 : ℝ)) = 0 := by simp
  rw [h_rhs] at h
  exact le_antisymm (le_trans le_add_self h) (zero_le _)

/-- Form identity at f=0: the resolvent of zero has zero L² norm. -/
example (Λ : ℝ) (hLam : 1 < Λ) :
    (∫⁻ u, ‖(kato_operator Λ hLam).resolvent 0 u‖₊ ^ (2 : ℝ)) = 0 := by
  have h := (kato_operator Λ hLam).form_identity 0
  have h_rhs : (∫⁻ u, ‖(0 : ℝ → ℂ) u‖₊ ^ (2 : ℝ)) = 0 := by simp
  rw [h_rhs] at h
  exact le_antisymm (le_trans le_self_add h) (zero_le _)

/-! ## 5. Frequency moment control at ξ = 0

The axiom says log(2 + |ξ|) ≤ a + b · ψ_λ(ξ) for all ξ.
We know ψ_λ(0) = 0 (proved without axioms).
At ξ = 0: log 2 ≤ a. Combined with 0 < a from the axiom,
this is consistent (log 2 ≈ 0.693). -/

/-- At ξ=0, frequency moment control reduces to log 2 ≤ a, which is
    consistent with the axiom's guarantee that 0 < a. -/
example (Λ : ℝ) (hLam : 1 < Λ) :
    ∃ a b : ℝ, Real.log 2 ≤ a ∧ 0 < b := by
  obtain ⟨a, b, ha, hb, hξ⟩ := frequency_moment_control Λ hLam
  refine ⟨a, b, ?_, hb⟩
  have h0 := hξ 0
  simp only [abs_zero, add_zero, fourierSymbol_zero, mul_zero] at h0
  exact h0

/-! ## 6. Fourier symbol growth excludes ξ = 0

The axiom fourierSymbol_ge_log says ψ_λ(ξ) ≥ c₁ log|ξ| - c₂ for |ξ| ≥ ξ₀.
Since ξ₀ ≥ 2, the bound does NOT apply at ξ = 0 where ψ_λ(0) = 0.
Verify the exclusion zone is well-defined. -/

/-- The growth bound's exclusion zone starts at ξ₀ ≥ 2, safely excluding
    the zero of ψ_λ at ξ = 0. -/
example (Λ : ℝ) (hLam : 1 < Λ) :
    ∃ ξ₀ : ℝ, 2 ≤ ξ₀ ∧ ¬(ξ₀ ≤ |(0 : ℝ)|) := by
  obtain ⟨_, _, _, ξ₀, hξ₀, _⟩ := fourierSymbol_ge_log Λ hLam
  exact ⟨ξ₀, hξ₀, by simp; linarith⟩

/-! ## 7. Resolvent maps zero to form domain (axiom self-consistency)

The kato_operator axiom's structure guarantees resolvent maps any f to the
form domain. At f=0, combined with the form identity forcing energy = 0,
the resolvent output is in the domain with zero energy. -/

/-- The resolvent of zero is in the form domain (from axiom structure field)
    and has zero energy (from cross-check #4). These are consistent. -/
example (Λ : ℝ) (hLam : 1 < Λ) :
    (kato_operator Λ hLam).resolvent 0 ∈ formDomain Λ :=
  (kato_operator Λ hLam).resolvent_maps_to_domain 0

end
