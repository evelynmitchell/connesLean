/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fourier Symbol Lower Bounds

Reference: lamportform.tex, Section 7.2, lines 940–1057 (Lemmas 10–11, Corollary 12).

This file establishes lower bounds on the Fourier symbol ψ_λ(ξ):
- `archWeight_ge_inv_two_t`: w(t) ≥ 1/(2t) for t ∈ (0,1] (Lemma 10)
- `fourierSymbol_ge_log`: ψ_λ(ξ) ≥ c₁ log|ξ| - c₂ for large |ξ| (Lemma 11, axiomatized)
- `frequency_moment_control`: log(2+|ξ|) ≤ a + b·ψ_λ(ξ) (Corollary 12, axiomatized)
- `fourierSymbol_tendsto_atTop`: ψ_λ(ξ) → ∞ as ξ → +∞ (derived from Lemma 11)

The auxiliary lemmas `sinh_le_mul_cosh`, `exp_half_lt`, and `cosh_le_exp_half`
support the proof of the weight lower bound.
-/

import ConnesLean.Stage5.FourierSymbol
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fourier Symbol Lower Bounds

Establishes lower bounds on the Fourier symbol:
* `w(t) ≥ 1/(2t)` on `(0,1]` via hyperbolic inequalities (Lemma 10)
* `ψ_λ(ξ) ≥ c₁ log|ξ| - c₂` for large `|ξ|` (Lemma 11, axiomatized)
* `log(2+|ξ|) ≤ a + b · ψ_λ(ξ)` frequency moment control (Corollary 12, axiomatized)
* `ψ_λ(ξ) → ∞` as `ξ → +∞`

Reference: lamportform.tex, Section 7.2, lines 940–1057.
-/

namespace ConnesLean

open MeasureTheory Real Set Filter

noncomputable section

/-! ## Auxiliary lemmas for the weight lower bound -/

/-- `sinh t ≤ t · cosh t` for `t ≥ 0`.

    Proof: The function `g(t) = t · cosh t - sinh t` satisfies `g(0) = 0` and
    `g'(t) = t · sinh t ≥ 0` for `t ≥ 0`, so `g` is monotone on `[0, ∞)`.

    This is the key step in showing `sinh t ≤ t · exp (t/2)` and hence
    `w(t) = exp(t/2)/(2 sinh t) ≥ 1/(2t)`. -/
theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.cosh t := by
  suffices h : 0 ≤ t * Real.cosh t - Real.sinh t by linarith
  let g : ℝ → ℝ := fun x => x * Real.cosh x - Real.sinh x
  have hg0 : g 0 = 0 := by
    change 0 * Real.cosh 0 - Real.sinh 0 = 0
    rw [zero_mul, Real.sinh_zero, sub_self]
  have hg_cont : ContinuousOn g (Icc 0 t) :=
    (continuousOn_id.mul Real.continuous_cosh.continuousOn).sub
      Real.continuous_sinh.continuousOn
  have hg_diff : DifferentiableOn ℝ g (interior (Icc 0 t)) := by
    intro x _
    exact ((differentiableAt_id.mul Real.differentiable_cosh.differentiableAt).sub
      Real.differentiable_sinh.differentiableAt).differentiableWithinAt
  have hg_deriv : ∀ x ∈ interior (Icc 0 t), 0 ≤ deriv g x := by
    intro x hx
    rw [interior_Icc] at hx
    have hd : HasDerivAt g (x * Real.sinh x) x := by
      have h1 := (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
      have h2 := Real.hasDerivAt_sinh x
      have : HasDerivAt g (1 * Real.cosh x + x * Real.sinh x - Real.cosh x) x := h1.sub h2
      convert this using 1; ring
    rw [hd.deriv]
    exact mul_nonneg (le_of_lt hx.1) (Real.sinh_nonneg_iff.mpr (le_of_lt hx.1))
  have hg_mono := monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hg_cont hg_diff hg_deriv
  have := hg_mono (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  rw [hg0] at this
  exact this

/-- For `t ≤ 1`, `exp(t/2) < 5/3`.

    From `exp(1) < 2.72 < 25/9 = (5/3)²`, so `exp(1/2)² = exp(1) < 25/9`,
    hence `exp(1/2) < 5/3` (both positive). For `t ≤ 1`, monotonicity gives
    `exp(t/2) ≤ exp(1/2) < 5/3`. -/
lemma exp_half_lt {t : ℝ} (ht1 : t ≤ 1) : Real.exp (t / 2) < 5 / 3 := by
  have h1 : Real.exp (t / 2) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (1 / 2) < 5 / 3 := by
    have h_sq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h_e_lt : Real.exp 1 < 25 / 9 := by linarith [Real.exp_one_lt_d9]
    nlinarith [sq_nonneg (Real.exp (1 / 2) - 5 / 3)]
  linarith

/-- `cosh t ≤ exp(t/2)` for `t ∈ [0, 1]`.

    Key algebraic idea: set `v = exp(t/2)`, then the inequality
    `(v² + v⁻²)/2 ≤ v` is equivalent to `v⁴ + 1 ≤ 2v³`,
    which factors as `-(v-1)(v³ - v² - v - 1) ≥ 0`. For `v ∈ [1, 5/3)`,
    `v²(v-1) < 50/27 < 2 ≤ v+1` ensures the second factor is nonpositive. -/
theorem cosh_le_exp_half {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.cosh t ≤ Real.exp (t / 2) := by
  rw [Real.cosh_eq]
  set v := Real.exp (t / 2) with hv_def
  have hv_pos : 0 < v := Real.exp_pos _
  have hv_ge : 1 ≤ v := Real.one_le_exp (by linarith)
  have hv_lt : v < 5 / 3 := exp_half_lt ht1
  have hexp_t : Real.exp t = v * v := by
    rw [hv_def, ← Real.exp_add]; ring_nf
  have hexp_neg_t : Real.exp (-t) = (v * v)⁻¹ := by
    rw [hv_def, Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [hexp_t, hexp_neg_t]
  have hv_ne : v ≠ 0 := ne_of_gt hv_pos
  have key : v ^ 4 + 1 ≤ 2 * v ^ 3 := by
    have : v ^ 2 < (5 / 3) ^ 2 := by nlinarith
    nlinarith [sq_nonneg v, sq_nonneg (v - 1)]
  -- (v*v + (v*v)⁻¹)/2 ≤ v  ↔  v^4 + 1 ≤ 2*v^3  (after clearing v^2 > 0 and 2)
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), ← sub_nonneg]
  have h_eq : v * 2 - (v * v + (v * v)⁻¹) = (2 * v ^ 3 - v ^ 4 - 1) / v ^ 2 := by
    field_simp; ring
  rw [h_eq]
  exact div_nonneg (by linarith) (by positivity)

/-! ## Weight lower bound (Lemma 10) -/

/-- The archimedean weight satisfies `w(t) ≥ 1/(2t)` for `t ∈ (0, 1]`.

    **Proof chain:**
    1. `sinh t ≤ t · cosh t` (from `sinh_le_mul_cosh`)
    2. `cosh t ≤ exp(t/2)` for `t ∈ [0,1]` (from `cosh_le_exp_half`)
    3. Hence `sinh t ≤ t · exp(t/2)`, so `exp(t/2) / (2 sinh t) ≥ 1/(2t)`.

    Reference: lamportform.tex, Lemma 10 (line 940). -/
theorem archWeight_ge_inv_two_t {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1 / (2 * t) ≤ archWeight t := by
  unfold archWeight
  have h_chain : Real.sinh t ≤ t * Real.exp (t / 2) :=
    calc Real.sinh t
        ≤ t * Real.cosh t := sinh_le_mul_cosh (le_of_lt ht)
      _ ≤ t * Real.exp (t / 2) :=
        mul_le_mul_of_nonneg_left (cosh_le_exp_half (le_of_lt ht) ht1) (le_of_lt ht)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-! ## Logarithmic growth (Lemma 11, axiomatized) -/

/-- Logarithmic growth of the Fourier symbol: for `λ > 1`, there exist
    constants `c₁ > 0`, `c₂`, and `ξ₀ ≥ 2` such that
    `ψ_λ(ξ) ≥ c₁ log|ξ| - c₂` for all `|ξ| ≥ ξ₀`.

    **Proof sketch** (lamportform.tex, Lemma 11, lines 964–1021):
    1. Drop the nonneg prime sum; restrict arch integral to `(0, min(1,2L))`.
    2. Apply `archWeight_ge_inv_two_t`: `ψ_λ(ξ) ≥ 4c₀ ∫₀^{t₀} (1/t) sin²(ξt/2) dt`.
    3. Substitute `u = ξt/2`, partition `[0, R]` into π-intervals where `sin² ≥ 1/2`.
    4. Sum `≥ H_N/2 ≥ log(N)/2` where `N ~ |ξ|` (harmonic series lower bound).

    **Why axiom:** All building blocks exist in Mathlib (`integral_sin_sq`,
    `log_le_harmonic_floor`, substitution lemmas) but assembly requires 150+ lines
    of integral manipulation.

    **Soundness:** Sole precondition is `1 < cutoffLambda`, matching Lemma 11.
    The existential conclusion (∃ c₁ c₂ ξ₀) cannot be vacuously satisfied.
    No structure parameters. -/
axiom fourierSymbol_ge_log (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∃ ξ₀ : ℝ, 2 ≤ ξ₀ ∧
      ∀ ξ : ℝ, ξ₀ ≤ |ξ| → c₁ * Real.log |ξ| - c₂ ≤ fourierSymbol cutoffLambda ξ

/-! ## Frequency moment control (Corollary 12, axiomatized) -/

/-- Energy controls a logarithmic frequency moment: there exist `a, b > 0` such that
    `log(2 + |ξ|) ≤ a + b · ψ_λ(ξ)` for all `ξ`.

    **Proof sketch** (lamportform.tex, Corollary 12, lines 1023–1057):
    - For `|ξ| ≥ ξ₀`: `log(2+|ξ|) ≤ log(3|ξ|) ≤ (ψ_λ(ξ) + c₂)/c₁ + log 3`
      (from `fourierSymbol_ge_log`).
    - For `|ξ| < ξ₀`: `log(2+|ξ|) ≤ log(2+ξ₀)`, a finite constant.
    - Set `b = 1/c₁`, `a = c₂/c₁ + log 3 + log(2+ξ₀)`.

    The integral version (multiplying by `|φ̂(ξ)|²` and integrating) is deferred
    to the Fourier representation PR.

    **Soundness:** Sole precondition is `1 < cutoffLambda`, matching
    Corollary 12. The existential conclusion (∃ a b with positivity) cannot
    be vacuously satisfied. No structure parameters. -/
axiom frequency_moment_control (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ ξ : ℝ, Real.log (2 + |ξ|) ≤ a + b * fourierSymbol cutoffLambda ξ

/-! ## Derived: Fourier symbol tends to infinity -/

/-- The Fourier symbol tends to `+∞` as `ξ → +∞`.

    Derived from `fourierSymbol_ge_log`: for any bound `B`, choose
    `ξ₁ = max(ξ₀, exp((B + c₂)/c₁))`, then for `ξ ≥ ξ₁`,
    `ψ_λ(ξ) ≥ c₁ log ξ - c₂ ≥ B`.

    Combined with `fourierSymbol_even`, this gives `ψ_λ(ξ) → ∞` as `|ξ| → ∞`. -/
theorem fourierSymbol_tendsto_atTop (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    Tendsto (fun ξ => fourierSymbol cutoffLambda ξ) atTop atTop := by
  obtain ⟨c₁, c₂, hc₁, ξ₀, hξ₀, hbound⟩ := fourierSymbol_ge_log cutoffLambda hLam
  rw [tendsto_atTop_atTop]
  intro B
  use max ξ₀ (Real.exp ((B + c₂) / c₁))
  intro ξ hξ
  have hξ_ge_ξ₀ : ξ₀ ≤ ξ := le_trans (le_max_left _ _) hξ
  have hξ_ge_exp : Real.exp ((B + c₂) / c₁) ≤ ξ := le_trans (le_max_right _ _) hξ
  have hξ_pos : 0 < ξ := lt_of_lt_of_le (by linarith : 0 < ξ₀) hξ_ge_ξ₀
  have hξ_abs : |ξ| = ξ := abs_of_pos hξ_pos
  have h_log : (B + c₂) / c₁ ≤ Real.log ξ := by
    rw [← Real.log_exp ((B + c₂) / c₁)]
    exact Real.log_le_log (Real.exp_pos _) hξ_ge_exp
  have h_mul : B + c₂ ≤ c₁ * Real.log ξ := by
    have := (div_le_iff₀ hc₁).mp h_log
    linarith [mul_comm c₁ (Real.log ξ)]
  calc B ≤ c₁ * Real.log ξ - c₂ := by linarith
    _ = c₁ * Real.log |ξ| - c₂ := by rw [hξ_abs]
    _ ≤ fourierSymbol cutoffLambda ξ :=
        hbound ξ (by rw [hξ_abs]; exact hξ_ge_ξ₀)

end

end ConnesLean
