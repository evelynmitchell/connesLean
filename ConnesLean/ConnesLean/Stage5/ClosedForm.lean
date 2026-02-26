/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closed Energy Form and Form Domain

Reference: lamportform.tex, Section 7.3, lines 844–936 (Propositions 6–7, Lemma 9).

This file defines the closed energy form structure for the restricted Weil quadratic form:
- `formDomain`: the set of functions with finite energy E_λ(G) ≠ ⊤
- `IsClosedEnergyForm`: Kato closed-form structure (nonneg, dense domain, graph complete)
- `energyForm_eq_fourierSymbol_integral`: Fourier representation E_λ(G) = (1/2π) ∫ ψ_λ|Ĝ|² dξ
- `formDomain_eq_weighted_fourier`: domain characterization via weighted Fourier space
- `energyForm_closed_on_line`: closedness on L²(ℝ) (Proposition 6)
- `energyForm_closed_on_interval`: closedness on L²(I) (Proposition 7)

The quadratic form E_λ is symmetric in the sense that its polarization
B(f,g) = (E(f+g) - E(f-g))/4 is automatically symmetric; no separate field is needed.
-/

import ConnesLean.Stage5.SymbolLowerBound
import ConnesLean.Stage2.EnergyForm
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space

namespace ConnesLean

open MeasureTheory Real Set Filter

noncomputable section

/-! ## Form domain -/

/-- The form domain D(E_λ) is the set of functions with finite energy.

    A function G belongs to D(E_λ) when its energy `energyForm cutoffLambda G`,
    valued in `ENNReal`, is not `⊤`. This is the natural domain for the
    quadratic form E_λ. -/
def formDomain (cutoffLambda : ℝ) : Set (ℝ → ℂ) :=
  {G : ℝ → ℂ | energyForm cutoffLambda G ≠ ⊤}

/-! ## Closed form structure -/

/-- A Kato closed-form structure for E_λ (cf. Kato, Thm VI.1.17).

    Fields:
    - `nonneg`: E_λ(G) ≥ 0 (trivial for ENNReal)
    - `zero_energy`: E_λ(0) = 0
    - `smooth_in_domain`: C_c^∞ ⊂ D(E_λ) (dense domain)
    - `graph_complete`: if (Gn) is Cauchy in the graph norm
      ‖G‖² + E_λ(G) and converges in L², then the limit is in D(E_λ)
      and E_λ(Gn − G) → 0 -/
structure IsClosedEnergyForm (cutoffLambda : ℝ) : Prop where
  nonneg : ∀ G : ℝ → ℂ, (0 : ENNReal) ≤ energyForm cutoffLambda G
  zero_energy : energyForm cutoffLambda 0 = 0
  smooth_in_domain : ∀ G : ℝ → ℂ, HasCompactSupport G → ContDiff ℝ ⊤ G →
    G ∈ formDomain cutoffLambda
  graph_complete : ∀ (Gn : ℕ → ℝ → ℂ) (G : ℝ → ℂ),
    (∀ n, Gn n ∈ formDomain cutoffLambda) →
    Filter.Tendsto (fun n => ∫⁻ u, ‖Gn n u - G u‖₊ ^ (2 : ℝ)) atTop (nhds 0) →
    (∀ ε : ENNReal, 0 < ε → ∃ N, ∀ n m, N ≤ n → N ≤ m →
      energyForm cutoffLambda (fun u => Gn n u - Gn m u) < ε) →
    G ∈ formDomain cutoffLambda ∧
    Filter.Tendsto (fun n => energyForm cutoffLambda (fun u => Gn n u - G u)) atTop (nhds 0)

/-! ## Fourier representation (Lemma 9, axiomatized) -/

/-- Fourier representation of the energy form:
    `E_λ(G) = (1/2π) ∫ ψ_λ(ξ) |Ĝ(ξ)|² dξ`.

    **Proof sketch** (lamportform.tex, Lemma 9, lines 844–872):
    Write ‖G − S_t G‖² = (1/2π) ∫ 4 sin²(ξt/2) |Ĝ(ξ)|² dξ (Plancherel),
    substitute into the archimedean integral and prime sum, interchange
    integration order (Fubini), and recognize `fourierSymbol`.

    **Why axiom:** Requires Plancherel theorem (not in Mathlib) and
    Fubini interchange for the double integral. -/
axiom energyForm_eq_fourierSymbol_integral (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (G : ℝ → ℂ) (hG : G ∈ formDomain cutoffLambda) :
    (energyForm cutoffLambda G).toReal =
    (1 / (2 * Real.pi)) *
    ∫ ξ, fourierSymbol cutoffLambda ξ * ‖FourierTransform.fourier G ξ‖ ^ 2

/-! ## Domain characterization (Proposition 6, Step 2, axiomatized) -/

/-- The form domain equals the weighted Fourier space:
    `G ∈ D(E_λ) ↔ G ∈ L² ∧ ∫ ψ_λ(ξ)|Ĝ(ξ)|² dξ < ∞`.

    This is immediate from the Fourier representation: `E_λ(G) < ∞` iff the
    weighted integral converges, and convergence of `∫ ψ_λ|Ĝ|²` requires `Ĝ ∈ L²`
    (since `ψ_λ ≥ 0`).

    **Why axiom:** Depends on the Fourier representation axiom. -/
axiom formDomain_eq_weighted_fourier (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (G : ℝ → ℂ) :
    G ∈ formDomain cutoffLambda ↔
    (∫⁻ ξ, ↑‖FourierTransform.fourier G ξ‖₊ ^ 2 < ⊤ ∧
     ∫⁻ ξ, ↑(fourierSymbol cutoffLambda ξ).toNNReal *
       ↑‖FourierTransform.fourier G ξ‖₊ ^ 2 < ⊤)

/-! ## Closedness on L²(ℝ) (Proposition 6, axiomatized) -/

/-- The energy form E_λ is a closed form on L²(ℝ) in the sense of Kato.

    **Proof sketch** (lamportform.tex, Proposition 6, lines 874–907):
    - `nonneg`: trivial (ENNReal).
    - `zero_energy`: from `energyForm_zero`.
    - `smooth_in_domain`: for φ ∈ C_c^∞, ‖φ − S_t φ‖ ≤ |t|·‖φ'‖ (MVT), so the
      energy integral converges by integrability of w(t)·t².
    - `graph_complete`: the graph norm ‖G‖_E² = ‖G‖² + E_λ(G) equals
      (1/2π) ∫ (1 + ψ_λ(ξ)) |Ĝ(ξ)|² dξ, a weighted L² norm. Completeness
      of weighted L² spaces gives the result.

    **Why axiom:** `smooth_in_domain` needs the MVT translation estimate plus
    integrability of w(t)t². `graph_complete` needs weighted L² completeness
    via Fourier isometry. Both depend on Plancherel. -/
axiom energyForm_closed_on_line (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    IsClosedEnergyForm cutoffLambda

/-! ## Closedness on L²(I) (Proposition 7, axiomatized) -/

/-- The energy form E_λ is closed on L²(I) where I = [−log λ, log λ].

    If (Gn) are supported in I = Icc(−L, L), Cauchy in graph norm, and
    converge in L² to G, then G is supported in I and belongs to D(E_λ).

    **Proof sketch** (lamportform.tex, Proposition 7, lines 909–936):
    The subspace H_I = {φ ∈ L²(ℝ) : supp(φ) ⊆ Icc(−L,L)} is closed in L²(ℝ).
    Since Gn → G in L² with each Gn supported in I, the limit G is supported in I.
    Proposition 6 (closedness on ℝ) gives G ∈ D(E_λ).

    **Why axiom:** Needs H_I closed in L²(ℝ) + Proposition 6. Standard but
    requires ~80 lines of L² machinery. -/
axiom energyForm_closed_on_interval (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    ∀ (Gn : ℕ → ℝ → ℂ) (G : ℝ → ℂ),
    let L := Real.log cutoffLambda
    (∀ n, Function.support (Gn n) ⊆ Icc (-L) L) →
    (∀ n, Gn n ∈ formDomain cutoffLambda) →
    Filter.Tendsto (fun n => ∫⁻ u, ‖Gn n u - G u‖₊ ^ (2 : ℝ)) atTop (nhds 0) →
    (∀ ε : ENNReal, 0 < ε → ∃ N, ∀ n m, N ≤ n → N ≤ m →
      energyForm cutoffLambda (fun u => Gn n u - Gn m u) < ε) →
    Function.support G ⊆ Icc (-L) L ∧ G ∈ formDomain cutoffLambda

/-! ## Proved theorems -/

/-- The zero function belongs to the form domain. -/
theorem zero_mem_formDomain (cutoffLambda : ℝ) :
    (0 : ℝ → ℂ) ∈ formDomain cutoffLambda := by
  simp [formDomain, energyForm_zero]

/-- The form domain is nonempty (contains the zero function). -/
theorem formDomain_nonempty (cutoffLambda : ℝ) :
    (formDomain cutoffLambda).Nonempty :=
  ⟨0, zero_mem_formDomain cutoffLambda⟩

/-- The integrand ψ_λ(ξ) · ‖Ĝ(ξ)‖² in the Fourier representation is nonneg. -/
theorem energyForm_fourierSymbol_nonneg (cutoffLambda : ℝ) (G : ℝ → ℂ) (ξ : ℝ) :
    0 ≤ fourierSymbol cutoffLambda ξ * ‖FourierTransform.fourier G ξ‖ ^ 2 :=
  mul_nonneg (fourierSymbol_nonneg cutoffLambda ξ) (sq_nonneg _)

end

end ConnesLean
