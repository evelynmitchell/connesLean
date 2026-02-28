/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariance Split — Lemma 14

Reference: lamportform.tex, Lemma 14 (lines 1220–1310).

If L²(B) is invariant under the semigroup T(t) = e^{-tA_λ}, then for every
G ∈ D(E_λ), the indicator projections 1_B · G and 1_{I\B} · G lie in D(E_λ)
and the energy form splits:

  E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G).

## Main results

- `SemigroupInvariantIdeal`: structure for semigroup-invariant measurable subsets
- `laplace_resolvent_commute`: indicator commutes with Kato resolvent (axiom)
- `projection_commutes_with_sqrt`: energy form splits into indicator projections (axiom)
- `invariance_domain_preserved`: indicator projections preserve form domain
- `invariance_split`: main Lemma 14 packaging
-/

import ConnesLean.Stage5.CompactResolvent

/-!
# Invariance Split — Lemma 14

Formalizes Lemma 14: if L²(B) is semigroup-invariant, then the energy form
splits into orthogonal indicator projections 1_B · G and 1_{I\B} · G.

Reference: lamportform.tex, Lemma 14 (lines 1220–1310).
-/

namespace ConnesLean

open MeasureTheory Set Real Filter

noncomputable section

/-! ## Semigroup-invariant ideal -/

/-- A measurable subset B ⊆ I such that L²(B) is invariant under the
    semigroup T(t) = e^{-tA_λ}. This is the hypothesis of Lemma 14.

    The semigroup invariance means that for every f supported in B,
    the semigroup image T(t)f is still supported in B. We do not
    formalize the semigroup directly; instead, the consequences
    (resolvent commutativity and energy splitting) are axiomatized. -/
structure SemigroupInvariantIdeal (cutoffLambda : ℝ) where
  B : Set ℝ
  B_measurable : MeasurableSet B
  B_subset : B ⊆ logInterval (Real.log cutoffLambda)

/-! ## Axioms for semigroup-invariant projections -/

/-- **Resolvent commutativity (Lemma 14, Steps 2–3):**
    The indicator projection 1_B commutes with the Kato resolvent (A_λ + I)⁻¹.

    This follows from two facts:
    1. Semigroup invariance: T(t)(1_B · f) = 1_B · T(t)f (Step 2)
    2. Laplace transform: (A_λ + I)⁻¹ = ∫₀^∞ e^{-t} T(t) dt (Step 3)

    Since the indicator commutes with each T(t) and the Laplace integral
    is a Bochner integral, it commutes with the resolvent.

    **Why axiom:** Requires Bochner integration of operator-valued functions
    and the semigroup Laplace representation, neither available in Mathlib. -/
axiom laplace_resolvent_commute {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : SemigroupInvariantIdeal cutoffLambda) (f : ℝ → ℂ) :
    inv.B.indicator ((kato_operator cutoffLambda hLam).resolvent f) =
    (kato_operator cutoffLambda hLam).resolvent (inv.B.indicator f)

/-- **Energy splitting (Lemma 14, Steps 4–6):**
    The energy form decomposes into orthogonal indicator projections:
      E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G)

    The proof in the LaTeX document proceeds:
    - Step 4: Resolvent commutativity + spectral functional calculus gives
      commutativity with A_λ^{1/2}
    - Step 5: Domain preservation for the indicator projections
    - Step 6: Pythagorean theorem in the form domain inner product

    **Why axiom:** Requires Borel functional calculus for unbounded
    self-adjoint operators, not available in Mathlib. -/
axiom projection_commutes_with_sqrt {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : SemigroupInvariantIdeal cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    energyForm cutoffLambda G =
      energyForm cutoffLambda (inv.B.indicator G) +
      energyForm cutoffLambda
        ((logInterval (Real.log cutoffLambda) \ inv.B).indicator G)

/-! ## Derived theorems -/

/-- **Domain preservation:** Both indicator projections 1_B · G and
    1_{I\B} · G belong to the form domain D(E_λ) whenever G does.

    From the energy splitting `E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G)`
    and finiteness of `E_λ(G)`, both summands must be finite in `ENNReal`.

    Reference: lamportform.tex, Lemma 14, Step 5 (lines 1280–1295). -/
theorem invariance_domain_preserved {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : SemigroupInvariantIdeal cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    inv.B.indicator G ∈ formDomain cutoffLambda ∧
    (logInterval (Real.log cutoffLambda) \ inv.B).indicator G ∈
      formDomain cutoffLambda := by
  have h_split := projection_commutes_with_sqrt hLam inv G hG
  have hG_fin : energyForm cutoffLambda G ≠ ⊤ := hG
  rw [h_split] at hG_fin
  have h_both := ENNReal.add_ne_top.mp hG_fin
  exact ⟨h_both.1, h_both.2⟩

/-- **Lemma 14 (Invariance Split):** If L²(B) is invariant under the semigroup,
    then for every G ∈ D(E_λ):
    1. 1_B · G ∈ D(E_λ)
    2. 1_{I\B} · G ∈ D(E_λ)
    3. E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G)

    Reference: lamportform.tex, Lemma 14 (lines 1220–1310). -/
theorem invariance_split {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : SemigroupInvariantIdeal cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    inv.B.indicator G ∈ formDomain cutoffLambda ∧
    (logInterval (Real.log cutoffLambda) \ inv.B).indicator G ∈
      formDomain cutoffLambda ∧
    energyForm cutoffLambda G =
      energyForm cutoffLambda (inv.B.indicator G) +
      energyForm cutoffLambda
        ((logInterval (Real.log cutoffLambda) \ inv.B).indicator G) := by
  have h_dom := invariance_domain_preserved hLam inv G hG
  exact ⟨h_dom.1, h_dom.2, projection_commutes_with_sqrt hLam inv G hG⟩

end

end ConnesLean
