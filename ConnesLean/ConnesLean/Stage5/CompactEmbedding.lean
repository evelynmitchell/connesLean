/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Compact Embedding D(E_λ) ↪ L²(I)

Reference: lamportform.tex, lines 1061–1157 (Theorem KR, Lemma 13, Proposition 8).

This file defines the compact embedding of the form domain into L²(I):
- `IsRelativelyCompactL2`: sequential compactness in L²
- `formNormBall`: the graph-norm ball {φ : supp ⊆ I, ‖φ‖² + E_λ(φ) ≤ M}
- `kolmogorov_riesz_compact`: KR criterion for compactly supported L² functions
- `formNormBall_equicontinuous`: translation equicontinuity from form norm (Lemma 13)
- `formNormBall_isRelativelyCompactL2`: compact embedding (Proposition 8)
-/

import ConnesLean.Stage5.ClosedForm

namespace ConnesLean

open MeasureTheory Real Set Filter

noncomputable section

/-! ## Sequential L² compactness -/

/-- Sequential compactness in L²: every sequence in K has a subsequence
    converging in L² norm to some limit function.

    This is the sequential characterization of relative compactness in L²,
    used as the target property for the Kolmogorov-Riesz theorem. -/
def IsRelativelyCompactL2 (K : Set (ℝ → ℂ)) : Prop :=
  ∀ (φ : ℕ → ℝ → ℂ), (∀ n, φ n ∈ K) →
    ∃ (f : ℝ → ℂ) (σ : ℕ → ℕ), StrictMono σ ∧
      Filter.Tendsto (fun n => ∫⁻ u, ‖φ (σ n) u - f u‖₊ ^ (2 : ℝ)) atTop (nhds 0)

/-! ## Form-norm ball -/

/-- The form-norm ball: functions supported in I = [−log λ, log λ] with
    bounded graph norm ‖φ‖² + E_λ(φ) ≤ M.

    This is the unit ball of the graph norm restricted to functions
    supported in the interval I. The Kolmogorov-Riesz theorem will show
    this set is relatively compact in L²(I). -/
def formNormBall (cutoffLambda : ℝ) (M : ENNReal) : Set (ℝ → ℂ) :=
  {φ : ℝ → ℂ |
    Function.support φ ⊆ Icc (-(Real.log cutoffLambda)) (Real.log cutoffLambda) ∧
    (∫⁻ u, ‖φ u‖₊ ^ (2 : ℝ)) + energyForm cutoffLambda φ ≤ M}

/-! ## Kolmogorov-Riesz criterion and compact embedding -/

/-- Kolmogorov-Riesz compactness criterion for compactly supported L² functions.
    If K is a set of functions supported in [−R, R] with uniformly bounded L² norms
    and translation equicontinuity, then K is relatively compact in L².

    Reference: Brezis, Corollary 4.27. The compact support condition subsumes
    the general tightness condition. -/
axiom kolmogorov_riesz_compact (K : Set (ℝ → ℂ)) (R : ℝ)
    (h_supp : ∀ φ ∈ K, Function.support φ ⊆ Icc (-R) R)
    (h_bdd : ∃ M : ENNReal, M < ⊤ ∧ ∀ φ ∈ K, (∫⁻ u, ‖φ u‖₊ ^ (2 : ℝ)) ≤ M)
    (h_equi : ∀ ε : ENNReal, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ φ ∈ K, ∀ h : ℝ,
      |h| < δ → (∫⁻ u, ‖φ (u - h) - φ u‖₊ ^ (2 : ℝ)) < ε) :
    IsRelativelyCompactL2 K

/-- The form-norm ball satisfies translation equicontinuity: for any ε > 0,
    there exists δ > 0 such that all φ in the form-norm ball satisfy
    ‖τ_h φ − φ‖₂² < ε whenever |h| < δ.

    Reference: lamportform.tex, Lemma 13 (lines 1078–1127). Uses Plancherel
    and frequency splitting to convert the form-norm bound into equicontinuity. -/
axiom formNormBall_equicontinuous (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (M : ENNReal) (hM : M < ⊤) :
    ∀ ε : ENNReal, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ φ ∈ formNormBall cutoffLambda M, ∀ h : ℝ,
        |h| < δ → (∫⁻ u, ‖φ (u - h) - φ u‖₊ ^ (2 : ℝ)) < ε

/-! ## Proved theorems -/

/-- The zero function belongs to the form-norm ball for any M ≥ 0. -/
theorem zero_mem_formNormBall (cutoffLambda : ℝ) (M : ENNReal) :
    (0 : ℝ → ℂ) ∈ formNormBall cutoffLambda M := by
  constructor
  · simp only [Function.support_zero, empty_subset]
  · simp [energyForm_zero]

/-- The form-norm ball is nonempty (contains the zero function). -/
theorem formNormBall_nonempty (cutoffLambda : ℝ) (M : ENNReal) :
    (formNormBall cutoffLambda M).Nonempty :=
  ⟨0, zero_mem_formNormBall cutoffLambda M⟩

/-- The form-norm ball is monotone in M: if M ≤ M', then B(M) ⊆ B(M'). -/
theorem formNormBall_monotone (cutoffLambda : ℝ) {M M' : ENNReal} (h : M ≤ M') :
    formNormBall cutoffLambda M ⊆ formNormBall cutoffLambda M' := by
  intro φ ⟨hsupp, hbound⟩
  exact ⟨hsupp, le_trans hbound h⟩

/-- Every element of the form-norm ball (with M < ⊤) belongs to the form domain. -/
theorem formNormBall_subset_formDomain (cutoffLambda : ℝ) {M : ENNReal} (hM : M < ⊤) :
    formNormBall cutoffLambda M ⊆ formDomain cutoffLambda := by
  intro φ ⟨_, hbound⟩
  simp only [formDomain, Set.mem_setOf_eq]
  intro h_top
  rw [h_top, add_top, top_le_iff] at hbound
  exact absurd hbound (ne_of_lt hM)

/-- The form-norm ball is relatively compact in L²: the compact embedding
    D(E_λ) ↪ L²(I). Combines the Kolmogorov-Riesz criterion with the
    translation equicontinuity of the form-norm ball.

    Reference: lamportform.tex, Proposition 8 (lines 1129–1157). -/
theorem formNormBall_isRelativelyCompactL2 (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (M : ENNReal) (hM : M < ⊤) :
    IsRelativelyCompactL2 (formNormBall cutoffLambda M) :=
  kolmogorov_riesz_compact _ (Real.log cutoffLambda)
    (fun _ hφ => hφ.1)
    ⟨M, hM, fun _ hφ => le_trans le_self_add hφ.2⟩
    (formNormBall_equicontinuous cutoffLambda hLam M hM)

end

end ConnesLean
