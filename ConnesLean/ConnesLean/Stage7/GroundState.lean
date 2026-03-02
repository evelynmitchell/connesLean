/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Positivity Improving Semigroup & Ground State — Proposition 13

Reference: lamportform.tex, Proposition 13 and consequences (lines 1462–1556).

The translation semigroup T(t) = e^{-tA_λ} is positivity improving (Prop 13),
and A_λ has a simple ground state with strictly positive eigenfunction
(Perron-Frobenius, ATG Prop 2.4).

Two axioms consolidate the deep results:
1. `semigroup_positivity_improving`: FOT 1.4.1 + Kato IX.1.24 + ABHN Thm 2.3
2. `ground_state_simple`: ATG Prop 2.4 (Perron-Frobenius)

## Main results

- `IsPositivityImproving`: resolvent maps nonneg functions to strictly positive
- `GroundState`: structure carrying eigenvalue, eigenfunction, and spectral data
- `semigroup_positivity_improving`: axiom — T(t) is positivity improving
- `ground_state_simple`: axiom — Perron-Frobenius gives simple ground state
- `ground_state_exists`: result — chains axiom 1 → axiom 2
-/

import ConnesLean.Stage6.Irreducibility

/-!
# Positivity Improving Semigroup & Ground State

Formalizes Proposition 13 and its Perron-Frobenius consequences.

Reference: lamportform.tex, lines 1462–1556.
-/

namespace ConnesLean

open MeasureTheory Set Real Filter

noncomputable section

/-! ## Section 1: Positivity-improving predicate -/

/-- Resolvent positivity improving: the resolvent (A_λ + I)⁻¹ maps nonneg,
    nonzero, real-valued functions to strictly positive functions a.e. on I.

    Resolvent positivity improving is equivalent to semigroup positivity
    improving via the Laplace transform representation. Uses `logInterval`
    (= `Ioo (-L) L`) matching Stage 6 conventions.

    Reference: lamportform.tex, Proposition 13, Step 4 (line 1502). -/
def IsPositivityImproving (cutoffLambda : ℝ) (T : KatoOperator cutoffLambda) : Prop :=
  ∀ f : ℝ → ℂ,
    (∀ x, 0 ≤ (f x).re) →
    (∀ x, (f x).im = 0) →
    (∃ x ∈ logInterval (Real.log cutoffLambda), f x ≠ 0) →
    ∀ᵐ x ∂volume,
      x ∈ logInterval (Real.log cutoffLambda) →
      0 < (T.resolvent f x).re

/-! ## Section 2: Ground state structure -/

/-- Ground state data for A_λ: an eigenvalue μ₀ ≥ 0 and eigenfunction ψ₀
    that is strictly positive a.e., simple, and satisfies the resolvent
    eigenvalue equation (A_λ + I)⁻¹ψ₀ = (1/(μ₀+1))ψ₀.

    Reference: lamportform.tex, Proposition 13 consequence (lines 1530–1556). -/
structure GroundState (cutoffLambda : ℝ) (T : KatoOperator cutoffLambda) where
  eigenvalue : ℝ
  eigenfunction : ℝ → ℂ
  eigenvalue_nonneg : 0 ≤ eigenvalue
  eigenfunction_in_domain : eigenfunction ∈ formDomain cutoffLambda
  eigenfunction_nonzero : ∃ x, eigenfunction x ≠ 0
  eigenfunction_pos_ae :
    ∀ᵐ x ∂volume,
      x ∈ logInterval (Real.log cutoffLambda) →
      0 < (eigenfunction x).re
  resolvent_eigenvalue :
    ∀ᵐ x ∂volume,
      T.resolvent eigenfunction x =
        ((1 : ℝ) / (eigenvalue + 1)) • eigenfunction x
  eigenvalue_simple : ∀ (g : ℝ → ℂ),
    (∀ᵐ x ∂volume,
      T.resolvent g x =
        ((1 : ℝ) / (eigenvalue + 1)) • g x) →
    ∃ c : ℂ, ∀ᵐ x ∂volume, g x = c • eigenfunction x

/-! ## Section 3: Semigroup positivity improving (axiom) -/

/-- **Semigroup positivity improving (Proposition 13).**
    The translation semigroup T(t) = e^{-tA_λ} is positivity improving.

    The mathematical argument chains four deep results:
    1. Markov property (`energyForm_comp_normalContraction_le`, Stage 4)
       → Dirichlet form (FOT Definition 1.4.1)
    2. m-sectoriality → holomorphic semigroup (Kato, Theorem IX.1.24)
    3. Sub-Markov semigroup + irreducibility (`semigroup_irreducible`, Stage 6)
       → positivity improving (ABHN Theorem 2.3)
    4. Resolvent = Laplace transform of semigroup → resolvent positivity improving

    **Why axiom:** Requires Dirichlet form ↔ semigroup correspondence (FOT 1.4.1)
    and the Arendt-Batty-Hieber-Neubrander positivity theorem (ATG 2.3), neither
    available in Mathlib.

    **Soundness:** Sole precondition `1 < cutoffLambda` follows existing axiom
    convention. The conclusion `IsPositivityImproving` is non-trivially
    satisfiable: it requires the resolvent to map nonneg nonzero inputs to
    strictly positive outputs a.e. Precondition: `1 < cutoffLambda`. -/
axiom semigroup_positivity_improving (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    IsPositivityImproving cutoffLambda (kato_operator cutoffLambda hLam)

/-! ## Section 4: Ground state existence (axiom) -/

/-- **Simple ground state (Perron-Frobenius, ATG Proposition 2.4).**
    Positivity improving + compact resolvent → A_λ has a simple ground state:
    the bottom of the spectrum μ₀ ≥ 0 is a simple eigenvalue with a
    strictly positive eigenfunction.

    **Why axiom:** Requires the abstract Perron-Frobenius theorem for
    positivity-improving semigroups on L² spaces (ATG Proposition 2.4).
    This is a deep result in positive operator semigroup theory not
    available in Mathlib.

    **Soundness:** Takes `IsPositivityImproving` as an explicit hypothesis,
    which is non-trivially constructible (requires axiom 1 above). The
    `GroundState` conclusion has 7 nontrivial fields including domain
    membership, strict positivity a.e., resolvent eigenvalue equation,
    and simplicity. Preconditions: `1 < cutoffLambda` and
    `IsPositivityImproving`. -/
axiom ground_state_simple (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (h_pos : IsPositivityImproving cutoffLambda (kato_operator cutoffLambda hLam)) :
    GroundState cutoffLambda (kato_operator cutoffLambda hLam)

/-! ## Section 5: Main theorem -/

/-- **Ground state existence (Proposition 13 + Perron-Frobenius).**
    The operator A_λ has a simple ground state with strictly positive
    eigenfunction.

    Chains axiom 1 (positivity improving) into axiom 2 (Perron-Frobenius).

    Reference: lamportform.tex, lines 1530–1556. -/
def ground_state_exists (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    GroundState cutoffLambda (kato_operator cutoffLambda hLam) :=
  ground_state_simple cutoffLambda hLam
    (semigroup_positivity_improving cutoffLambda hLam)

/-! ## Section 6: Soundness tests -/

-- Test 1: ground_state_exists composes correctly
example (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    GroundState cutoffLambda (kato_operator cutoffLambda hLam) :=
  ground_state_exists cutoffLambda hLam

-- Test 2: eigenvalue is nonneg
example (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    0 ≤ (ground_state_exists cutoffLambda hLam).eigenvalue :=
  (ground_state_exists cutoffLambda hLam).eigenvalue_nonneg

-- Test 3: eigenfunction is in the form domain
example (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    (ground_state_exists cutoffLambda hLam).eigenfunction ∈ formDomain cutoffLambda :=
  (ground_state_exists cutoffLambda hLam).eigenfunction_in_domain

-- Test 4: eigenfunction is nonzero
example (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    ∃ x, (ground_state_exists cutoffLambda hLam).eigenfunction x ≠ 0 :=
  (ground_state_exists cutoffLambda hLam).eigenfunction_nonzero

-- Test 5: IsPositivityImproving composes with axiom 1
example (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    IsPositivityImproving cutoffLambda (kato_operator cutoffLambda hLam) :=
  semigroup_positivity_improving cutoffLambda hLam

end

end ConnesLean
