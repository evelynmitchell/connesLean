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

- `SemigroupInvariantIdeal`: structure encoding semigroup invariance via
  the energy splitting property
- `invariance_domain_preserved`: indicator projections preserve form domain
- `invariance_split`: main Lemma 14 packaging
-/

import ConnesLean.Stage5.CompactResolvent

/-!
# Invariance Split — Lemma 14

Formalizes Lemma 14: if L²(B) is semigroup-invariant, then the energy form
splits into orthogonal indicator projections 1_B · G and 1_{I\B} · G.

The semigroup invariance hypothesis is encoded as the `energy_split` field
of the `SemigroupInvariantIdeal` structure, which asserts the energy form
decomposition directly. This is the consequence of:
- Steps 2–3: Semigroup invariance → resolvent commutativity via Laplace transform
- Steps 4–6: Resolvent commutativity → A_λ^{1/2} commutativity via spectral
  functional calculus → energy splitting via Pythagorean theorem

These intermediate steps require Bochner integration of operator-valued
semigroups and Borel functional calculus for unbounded self-adjoint operators,
neither available in Mathlib.

Reference: lamportform.tex, Lemma 14 (lines 1220–1310).
-/

namespace ConnesLean

open MeasureTheory Set Real Filter

noncomputable section

/-! ## Semigroup-invariant ideal -/

/-- A measurable subset B ⊆ I such that L²(B) is invariant under the
    semigroup T(t) = e^{-tA_λ}, encoding Lemma 14's hypothesis.

    The `energy_split` field captures the consequence of semigroup invariance:
    the energy form decomposes into orthogonal indicator projections.
    The mathematical derivation (LaTeX Steps 2–6) proceeds:
    1. Semigroup invariance: T(t)(1_B · f) = 1_B · T(t)f
    2. Laplace transform: 1_B commutes with (A_λ + I)⁻¹
    3. Spectral functional calculus: 1_B commutes with A_λ^{1/2}
    4. Pythagorean theorem: E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G)

    These steps require operator-valued Bochner integration and Borel
    functional calculus, neither available in Mathlib.

    Reference: lamportform.tex, Lemma 14, Steps 1–6 (lines 1220–1310). -/
structure SemigroupInvariantIdeal (cutoffLambda : ℝ) where
  B : Set ℝ
  B_measurable : MeasurableSet B
  B_subset : B ⊆ logInterval (Real.log cutoffLambda)
  energy_split : ∀ (G : ℝ → ℂ), G ∈ formDomain cutoffLambda →
    energyForm cutoffLambda G =
      energyForm cutoffLambda (B.indicator G) +
      energyForm cutoffLambda
        ((logInterval (Real.log cutoffLambda) \ B).indicator G)

/-! ## Derived theorems -/

/-- **Domain preservation:** Both indicator projections 1_B · G and
    1_{I\B} · G belong to the form domain D(E_λ) whenever G does.

    From the energy splitting `E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G)`
    and finiteness of `E_λ(G)`, both summands must be finite in `ENNReal`.

    Reference: lamportform.tex, Lemma 14, Step 5 (lines 1280–1295). -/
theorem invariance_domain_preserved {cutoffLambda : ℝ}
    (inv : SemigroupInvariantIdeal cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    inv.B.indicator G ∈ formDomain cutoffLambda ∧
    (logInterval (Real.log cutoffLambda) \ inv.B).indicator G ∈
      formDomain cutoffLambda := by
  have h_split := inv.energy_split G hG
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
theorem invariance_split {cutoffLambda : ℝ}
    (inv : SemigroupInvariantIdeal cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    inv.B.indicator G ∈ formDomain cutoffLambda ∧
    (logInterval (Real.log cutoffLambda) \ inv.B).indicator G ∈
      formDomain cutoffLambda ∧
    energyForm cutoffLambda G =
      energyForm cutoffLambda (inv.B.indicator G) +
      energyForm cutoffLambda
        ((logInterval (Real.log cutoffLambda) \ inv.B).indicator G) := by
  have h_dom := invariance_domain_preserved inv G hG
  exact ⟨h_dom.1, h_dom.2, inv.energy_split G hG⟩

end

end ConnesLean
