/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semigroup Irreducibility — Proposition 10 & Corollary 15

Reference: lamportform.tex, Proposition 10 conclusion (line 1442) and
Corollary 15 (lines 1455–1460).

From CrossVanishing, every `EnergyFormSplit` has trivial B (null or conull).
This gives semigroup irreducibility. One axiom records the Schaefer III.1
classification of closed ideals, bridged via Lemma 14.

## Main results

- `IsSemigroupIrreducible`: predicate — every `EnergyFormSplit` has trivial B
- `invariant_ideal_trivial`: Proposition 10 conclusion (wrapper)
- `closed_ideal_classification`: axiom — Schaefer III.1 + Lemma 14 bridge
- `semigroup_irreducible`: Corollary 15 — the semigroup is irreducible
-/

import ConnesLean.Stage6.CrossVanishing

/-!
# Semigroup Irreducibility

Wraps the invariant ideal null-or-conull result into a semigroup irreducibility
predicate, plus one axiom recording the Schaefer classification of closed ideals.

Reference: lamportform.tex, Proposition 10 (line 1442), Corollary 15 (lines 1455–1460).
-/

namespace ConnesLean

open MeasureTheory Set Real Filter

noncomputable section

/-! ## Section 1: Irreducibility predicate -/

/-- Semigroup irreducibility: every `EnergyFormSplit` has trivial B
    (either null or conull in the log-interval).

    Reference: lamportform.tex, Corollary 15 (line 1455). -/
structure IsSemigroupIrreducible (cutoffLambda : ℝ) : Prop where
  trivial_invariant_ideal :
    ∀ (inv : EnergyFormSplit cutoffLambda),
      volume inv.B = 0 ∨
      volume (logInterval (Real.log cutoffLambda) \ inv.B) = 0

/-! ## Section 2: Proposition 10 conclusion -/

/-- **Proposition 10 conclusion.** Every invariant ideal B arising from an
    `EnergyFormSplit` is either null or conull.

    Reference: lamportform.tex, Proposition 10 (line 1442). -/
theorem invariant_ideal_trivial {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    volume inv.B = 0 ∨
    volume (logInterval (Real.log cutoffLambda) \ inv.B) = 0 :=
  invariant_ideal_null_or_conull hLam inv

/-! ## Section 3: Closed ideal classification axiom -/

/-- **Closed ideal classification (Schaefer III.1 + Lemma 14 bridge).**
    If B ⊆ I is measurable and `1_B` is translation-invariant on I, then
    there exists an `EnergyFormSplit` with that B.

    The mathematical argument (lamportform.tex, Steps 2–6 of Lemma 14) derives
    energy splitting from semigroup invariance via: (1) Laplace transform →
    resolvent commutativity, (2) spectral functional calculus → A_λ^{1/2}
    commutativity, (3) Pythagorean theorem → energy splitting.

    **Why axiom:** Requires Bochner integration of operator-valued semigroups
    and Borel functional calculus for unbounded self-adjoint operators, neither
    available in Mathlib.

    **Soundness:** The `IndicatorTranslationInvariant` hypothesis prevents
    inconsistency: without it, one could produce `EnergyFormSplit` for
    arbitrary measurable B ⊆ I, proving every such B is null or conull
    (contradicting Lebesgue measure). The invariance guard restricts to
    genuinely semigroup-invariant ideals. Preconditions are `1 < cutoffLambda`,
    `MeasurableSet B`, `B ⊆ I`, and `IndicatorTranslationInvariant B I ε`. -/
axiom closed_ideal_classification (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (B : Set ℝ) (hB_meas : MeasurableSet B)
    (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (hB_inv : IndicatorTranslationInvariant B
      (logInterval (Real.log cutoffLambda))
      (2 * Real.log cutoffLambda)) :
    ∃ inv : EnergyFormSplit cutoffLambda, inv.B = B

/-! ## Section 4: Corollary 15 -/

/-- **Corollary 15: Semigroup irreducibility.** The translation semigroup on
    L²(I) is irreducible: every `EnergyFormSplit` has trivial B.

    Direct from the proof chain (does not use the axiom).

    Reference: lamportform.tex, Corollary 15 (lines 1455–1460). -/
theorem semigroup_irreducible {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    IsSemigroupIrreducible cutoffLambda where
  trivial_invariant_ideal inv := invariant_ideal_null_or_conull hLam inv

/-! ## Section 5: Soundness tests -/

-- Test 1: semigroup_irreducible composes correctly
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    IsSemigroupIrreducible cutoffLambda :=
  semigroup_irreducible hLam

-- Test 2: invariant_ideal_trivial composes with EnergyFormSplit
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    volume inv.B = 0 ∨
    volume (logInterval (Real.log cutoffLambda) \ inv.B) = 0 :=
  invariant_ideal_trivial hLam inv

-- Test 3: closed_ideal_classification takes the right types
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (B : Set ℝ) (hB_meas : MeasurableSet B)
    (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (hB_inv : IndicatorTranslationInvariant B
      (logInterval (Real.log cutoffLambda))
      (2 * Real.log cutoffLambda)) :
    ∃ inv : EnergyFormSplit cutoffLambda, inv.B = B :=
  closed_ideal_classification cutoffLambda hLam B hB_meas hB_sub hB_inv

end

end ConnesLean
