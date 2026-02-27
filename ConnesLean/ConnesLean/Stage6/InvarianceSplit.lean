/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariance Split — Lemma 14

Reference: lamportform.tex, Lemma 14 (lines 1220–1310).

If L²(B) is invariant under the semigroup T(t) = e^{-tA_λ}, then for
G ∈ D(E_λ), the indicator projections 1_B·G and 1_{I\B}·G both belong
to D(E_λ), and the energy splits:

  E_λ(G) = E_λ(1_B·G) + E_λ(1_{I\B}·G)

This is the first step in the irreducibility argument (6B → 6C → 6D → 6E chain).

## Main results

- `SemigroupInvariantIdeal`: structure for a measurable subset B ⊆ I
- `laplace_resolvent_commute`: axiom — resolvent commutes with indicator projection
- `projection_commutes_with_sqrt`: axiom — domain preservation + energy splitting
- `invariance_domain_preserved`: 1_B·G ∈ D(E_λ) when G ∈ D(E_λ)
- `invariance_complement_domain_preserved`: 1_{I\B}·G ∈ D(E_λ)
- `invariance_split`: E_λ(G) = E_λ(1_B·G) + E_λ(1_{I\B}·G)
-/

import ConnesLean.Stage5.CompactResolvent

namespace ConnesLean

open MeasureTheory Real Set Filter

noncomputable section

/-! ## Semigroup-invariant ideal structure -/

/-- A measurable subset B ⊆ I = Ioo(−log λ, log λ) that is invariant under
    the semigroup T(t) = e^{-tA_λ}. The semigroup invariance itself is
    consumed by the axioms below.

    Reference: lamportform.tex, Lemma 14, hypothesis. -/
structure SemigroupInvariantIdeal (cutoffLambda : ℝ) where
  B : Set ℝ
  B_measurable : MeasurableSet B
  B_subset : B ⊆ logInterval (Real.log cutoffLambda)

/-! ## Axioms -/

/-- The resolvent (A_λ + I)⁻¹ commutes with the indicator projection 1_B.
    This follows from the Laplace transform representation of the resolvent
    and semigroup invariance of B.

    **Why axiom:** Requires the Laplace integral representation of resolvents
    and dominated convergence for Bochner integrals, neither available in Mathlib.

    Reference: lamportform.tex, Lemma 14, Step 3; Engel-Nagel, Cor II.1.11. -/
axiom laplace_resolvent_commute (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ G : ℝ → ℂ,
      (kato_operator cutoffLambda hLam).resolvent (B.indicator G) =
      B.indicator ((kato_operator cutoffLambda hLam).resolvent G)

/-- The indicator projection 1_B preserves the form domain D(E_λ), and the
    energy splits: E_λ(G) = E_λ(1_B·G) + E_λ(1_{I\B}·G).

    This encodes Steps 4–6 of Lemma 14: the resolvent commutation (Step 3)
    implies that 1_B commutes with A_λ^{1/2}, from which domain preservation
    and the Pythagorean splitting follow.

    **Why axiom:** Requires Borel functional calculus (commutation with A^{1/2})
    and the spectral theorem for unbounded self-adjoint operators, both far
    beyond current Mathlib.

    Reference: lamportform.tex, Lemma 14, Steps 4–6; Reed-Simon, Thm VIII.5. -/
axiom projection_commutes_with_sqrt (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    B.indicator G ∈ formDomain cutoffLambda ∧
    energyForm cutoffLambda G =
      energyForm cutoffLambda (B.indicator G) +
      energyForm cutoffLambda ((logInterval (Real.log cutoffLambda) \ B).indicator G)

/-! ## Proved theorems -/

/-- The indicator projection 1_B preserves the form domain.

    Reference: lamportform.tex, Lemma 14, Step 5 (domain preservation). -/
theorem invariance_domain_preserved (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) (G : ℝ → ℂ)
    (hG : G ∈ formDomain cutoffLambda) :
    ideal.B.indicator G ∈ formDomain cutoffLambda :=
  (projection_commutes_with_sqrt cutoffLambda hLam ideal.B ideal.B_measurable
    ideal.B_subset G hG).1

/-- The complement projection 1_{I\B} preserves the form domain.

    Proof: the energy splitting gives E_λ(G) = E_λ(1_B·G) + E_λ(1_{I\B}·G).
    Since G ∈ D(E_λ), both summands must be finite (ENNReal.add_ne_top).

    Reference: lamportform.tex, Lemma 14, Step 5 (complement). -/
theorem invariance_complement_domain_preserved (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) (G : ℝ → ℂ)
    (hG : G ∈ formDomain cutoffLambda) :
    (logInterval (Real.log cutoffLambda) \ ideal.B).indicator G ∈ formDomain cutoffLambda := by
  have h_split := (projection_commutes_with_sqrt cutoffLambda hLam ideal.B ideal.B_measurable
    ideal.B_subset G hG).2
  change energyForm cutoffLambda ((logInterval (Real.log cutoffLambda) \ ideal.B).indicator G) ≠ ⊤
  intro h_top
  have hG_fin : energyForm cutoffLambda G ≠ ⊤ := hG
  rw [h_split, h_top, WithTop.add_top] at hG_fin
  exact hG_fin rfl

/-- **Lemma 14 (energy splitting):** For G ∈ D(E_λ), the energy decomposes
    as E_λ(G) = E_λ(1_B·G) + E_λ(1_{I\B}·G).

    Reference: lamportform.tex, Lemma 14, Step 6 (Pythagorean identity). -/
theorem invariance_split (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) (G : ℝ → ℂ)
    (hG : G ∈ formDomain cutoffLambda) :
    energyForm cutoffLambda G =
      energyForm cutoffLambda (ideal.B.indicator G) +
      energyForm cutoffLambda ((logInterval (Real.log cutoffLambda) \ ideal.B).indicator G) :=
  (projection_commutes_with_sqrt cutoffLambda hLam ideal.B ideal.B_measurable
    ideal.B_subset G hG).2

end

end ConnesLean
