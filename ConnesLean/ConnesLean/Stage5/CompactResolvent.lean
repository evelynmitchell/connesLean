/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Compact Resolvent for the Kato Operator A_λ

Reference: lamportform.tex, Theorem 9 (lines 1159–1209).

The closed energy form E_λ (Stage 5C) gives rise to a self-adjoint operator
A_λ ≥ 0 via the Kato representation theorem. We show A_λ has compact resolvent
by combining the Kato structure with the compact embedding D(E_λ) ↪ L²(I)
(Stage 5D).

## Main results

- `KatoOperator`: structure modeling the resolvent (A_λ + I)⁻¹
- `kato_operator`: axiomatized existence via the Kato representation theorem
- `HasCompactResolvent`: sequential compactness of the resolvent
- `resolvent_mem_formNormBall`: resolvent maps bounded L² functions into form-norm ball
- `compact_resolvent_of_compact_embedding`: main theorem — A_λ has compact resolvent
- `kato_resolvent_in_formDomain`: convenience wrapper for domain membership
-/

import ConnesLean.Stage5.CompactEmbedding

/-!
# Compact Resolvent for the Kato Operator A_λ

The closed energy form E_λ gives rise to a self-adjoint operator A_λ ≥ 0 via the
Kato representation theorem. Proves A_λ has compact resolvent by combining the
Kato structure with the compact embedding D(E_λ) ↪ L²(I).

Reference: lamportform.tex, Theorem 9 (lines 1159–1209).
-/

namespace ConnesLean

open MeasureTheory Real Set Filter

noncomputable section

/-! ## Kato operator structure -/

/-- Structure modeling the resolvent (A_λ + I)⁻¹ of a self-adjoint operator
    associated to the energy form E_λ via the Kato representation theorem.

    The three fields capture:
    1. The resolvent maps L² into the form domain D(E_λ)
    2. The resolvent preserves compact support in I = [−log λ, log λ]
    3. The form identity: ‖(A+I)⁻¹f‖² + E_λ((A+I)⁻¹f) ≤ ‖f‖²

    Reference: Kato, Perturbation Theory, Theorem VI.2.1. -/
structure KatoOperator (cutoffLambda : ℝ) where
  resolvent : (ℝ → ℂ) → (ℝ → ℂ)
  resolvent_maps_to_domain : ∀ f : ℝ → ℂ,
    resolvent f ∈ formDomain cutoffLambda
  resolvent_supported : ∀ f : ℝ → ℂ,
    Function.support f ⊆ Icc (-(Real.log cutoffLambda)) (Real.log cutoffLambda) →
    Function.support (resolvent f) ⊆ Icc (-(Real.log cutoffLambda)) (Real.log cutoffLambda)
  form_identity : ∀ f : ℝ → ℂ,
    (∫⁻ u, ‖resolvent f u‖₊ ^ (2 : ℝ)) + energyForm cutoffLambda (resolvent f) ≤
    (∫⁻ u, ‖f u‖₊ ^ (2 : ℝ))

/-! ## Kato representation theorem (axiomatized) -/

/-- The Kato representation theorem: every closed, densely defined, nonnegative
    symmetric form on a Hilbert space determines a unique self-adjoint operator.
    Applied to E_λ, this gives the operator A_λ ≥ 0 whose resolvent satisfies
    the form identity.

    **Why axiom:** The Kato representation theorem (Kato, Theorem VI.2.1) is
    deep functional analysis that is not available in Mathlib. The theorem
    requires:
    - E_λ is a closed form (Stage 5C: `energyForm_closed_on_line`)
    - E_λ is densely defined (follows from C_c^∞ ⊂ D(E_λ))
    - E_λ is nonneg (by construction as sum of L² norms)

    Reference: lamportform.tex, Theorem 9, Step 1 (lines 1164–1174). -/
axiom kato_operator (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    KatoOperator cutoffLambda

/-! ## Compact resolvent predicate -/

/-- Sequential characterization of compact resolvent: the resolvent (A_λ + I)⁻¹
    maps bounded L² sequences (supported in I) to sequences with L²-convergent
    subsequences.

    This is equivalent to saying the resolvent is a compact operator on L²(I),
    which in turn means A_λ has purely discrete spectrum with eigenvalues
    accumulating only at +∞.

    Reference: lamportform.tex, Theorem 9, Step 3 (lines 1192–1209). -/
def HasCompactResolvent (cutoffLambda : ℝ) (T : KatoOperator cutoffLambda) : Prop :=
  ∀ (f : ℕ → ℝ → ℂ) (C : ENNReal), C < ⊤ →
    (∀ n, (∫⁻ u, ‖f n u‖₊ ^ (2 : ℝ)) ≤ C) →
    (∀ n, Function.support (f n) ⊆
      Icc (-(Real.log cutoffLambda)) (Real.log cutoffLambda)) →
    ∃ (g : ℝ → ℂ) (σ : ℕ → ℕ), StrictMono σ ∧
      Filter.Tendsto
        (fun n => ∫⁻ u, ‖T.resolvent (f (σ n)) u - g u‖₊ ^ (2 : ℝ))
        atTop (nhds 0)

/-! ## Proved theorems -/

/-- The resolvent maps bounded, compactly supported L² functions into the
    form-norm ball. This is the key link between the Kato operator and the
    compact embedding: the form identity gives the graph-norm bound needed
    to land in `formNormBall`.

    Reference: lamportform.tex, Theorem 9, Steps 2.3–2.4 (lines 1183–1191). -/
theorem resolvent_mem_formNormBall (cutoffLambda : ℝ)
    (T : KatoOperator cutoffLambda) (f : ℝ → ℂ)
    (hsupp : Function.support f ⊆
      Icc (-(Real.log cutoffLambda)) (Real.log cutoffLambda))
    {C : ENNReal} (hbdd : (∫⁻ u, ‖f u‖₊ ^ (2 : ℝ)) ≤ C) :
    T.resolvent f ∈ formNormBall cutoffLambda C :=
  ⟨T.resolvent_supported f hsupp, le_trans (T.form_identity f) hbdd⟩

/-- **Main theorem (Theorem 9):** The operator A_λ has compact resolvent.

    The proof chains the Kato form identity with the compact embedding:
    1. Each resolvent image lands in the form-norm ball (by `resolvent_mem_formNormBall`)
    2. The form-norm ball is relatively compact in L² (by `formNormBall_isRelativelyCompactL2`)
    3. Therefore the resolvent sequence has a convergent subsequence

    Reference: lamportform.tex, Theorem 9, Step 3 (lines 1192–1209). -/
theorem compact_resolvent_of_compact_embedding (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    HasCompactResolvent cutoffLambda (kato_operator cutoffLambda hLam) := by
  intro f C hC hf_bdd hf_supp
  have h_compact := formNormBall_isRelativelyCompactL2 cutoffLambda hLam C hC
  let T := kato_operator cutoffLambda hLam
  have h_mem : ∀ n, T.resolvent (f n) ∈ formNormBall cutoffLambda C :=
    fun n => resolvent_mem_formNormBall cutoffLambda T (f n) (hf_supp n) (hf_bdd n)
  exact h_compact (fun n => T.resolvent (f n)) h_mem

/-- Convenience wrapper: the Kato resolvent maps any function into the form domain. -/
theorem kato_resolvent_in_formDomain (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (f : ℝ → ℂ) : (kato_operator cutoffLambda hLam).resolvent f ∈ formDomain cutoffLambda :=
  (kato_operator cutoffLambda hLam).resolvent_maps_to_domain f

end

end ConnesLean
