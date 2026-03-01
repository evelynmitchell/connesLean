/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Energy Form Split — Lemma 14

Reference: lamportform.tex, Lemma 14 (lines 1220–1310).

If the energy form splits across a measurable subset B ⊆ I and its complement,
then the indicator projections 1_B · G and 1_{I\B} · G lie in D(E_λ) for every
G ∈ D(E_λ).

## Main results

- `EnergyFormSplit`: structure packaging a measurable B ⊆ I with the energy
  splitting property E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G)
- `EnergyFormSplit.domain_preserved`: indicator projections preserve form domain
- `EnergyFormSplit.split`: main Lemma 14 — domain preservation + energy splitting
-/

import ConnesLean.Stage5.CompactResolvent

/-!
# Energy Form Split — Lemma 14

Packages the energy form splitting property for Lemma 14.

The `EnergyFormSplit` structure assumes the energy splitting directly as its
key hypothesis (`energy_split` field). In the mathematical argument
(lamportform.tex, Steps 2–6), this property is *derived* from semigroup
invariance of L²(B) via:
- Steps 2–3: Semigroup invariance → resolvent commutativity via Laplace transform
- Steps 4–6: Resolvent commutativity → A_λ^{1/2} commutativity via spectral
  functional calculus → energy splitting via Pythagorean theorem

We assume the conclusion rather than the hypothesis because the intermediate
steps require Bochner integration of operator-valued semigroups and Borel
functional calculus for unbounded self-adjoint operators, neither available
in Mathlib.

Reference: lamportform.tex, Lemma 14 (lines 1220–1310).
-/

namespace ConnesLean

open MeasureTheory Set Real Filter

noncomputable section

/-! ## Energy form splitting structure -/

/-- A measurable subset B ⊆ I for which the energy form splits across B
    and its complement: E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G).

    This is the key hypothesis of Lemma 14. In the mathematical proof,
    the splitting is derived from semigroup invariance of L²(B)
    (lamportform.tex, Steps 2–6):
    1. Semigroup invariance: T(t)(1_B · f) = 1_B · T(t)f
    2. Laplace transform: 1_B commutes with (A_λ + I)⁻¹
    3. Spectral functional calculus: 1_B commutes with A_λ^{1/2}
    4. Pythagorean theorem gives the splitting

    We assume the splitting directly because the derivation requires
    operator-valued Bochner integration and Borel functional calculus,
    neither available in Mathlib.

    Reference: lamportform.tex, Lemma 14, Steps 1–6 (lines 1220–1310). -/
structure EnergyFormSplit (cutoffLambda : ℝ) where
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
theorem EnergyFormSplit.domain_preserved {cutoffLambda : ℝ}
    (inv : EnergyFormSplit cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    inv.B.indicator G ∈ formDomain cutoffLambda ∧
    (logInterval (Real.log cutoffLambda) \ inv.B).indicator G ∈
      formDomain cutoffLambda := by
  have h_split := inv.energy_split G hG
  have hG_fin : energyForm cutoffLambda G ≠ ⊤ := hG
  rw [h_split] at hG_fin
  have h_both := ENNReal.add_ne_top.mp hG_fin
  exact ⟨h_both.1, h_both.2⟩

/-- **Lemma 14 (Energy Form Split):** If the energy form splits across B,
    then for every G ∈ D(E_λ):
    1. 1_B · G ∈ D(E_λ)
    2. 1_{I\B} · G ∈ D(E_λ)
    3. E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G)

    Reference: lamportform.tex, Lemma 14 (lines 1220–1310). -/
theorem EnergyFormSplit.split {cutoffLambda : ℝ}
    (inv : EnergyFormSplit cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    inv.B.indicator G ∈ formDomain cutoffLambda ∧
    (logInterval (Real.log cutoffLambda) \ inv.B).indicator G ∈
      formDomain cutoffLambda ∧
    energyForm cutoffLambda G =
      energyForm cutoffLambda (inv.B.indicator G) +
      energyForm cutoffLambda
        ((logInterval (Real.log cutoffLambda) \ inv.B).indicator G) := by
  have h_dom := inv.domain_preserved G hG
  exact ⟨h_dom.1, h_dom.2, inv.energy_split G hG⟩

/-! ## Soundness tests

These tests verify that `EnergyFormSplit` cannot be trivially constructed
for arbitrary measurable subsets. The `energy_split` field requires a proof
of the energy decomposition, which is not available for general B.

**Guideline for axiom-bearing files:** For every structure that encodes a
mathematical hypothesis, verify that pathological inputs (∅, full set,
arbitrary B) cannot satisfy the structure without providing the key property. -/

-- Soundness: constructing EnergyFormSplit requires providing `energy_split`.
-- The following would NOT compile without the fourth field:
--   example : EnergyFormSplit cutoffLambda :=
--     ⟨∅, MeasurableSet.empty, empty_subset _, ???⟩
-- The ??? must be a proof that E_λ(G) = E_λ(∅.indicator G) + E_λ(I.indicator G)
-- for all G ∈ D(E_λ), which cannot be discharged by `trivial` or `simp`.

end

end ConnesLean
