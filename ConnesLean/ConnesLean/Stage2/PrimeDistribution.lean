/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Prime Distribution W_p and Energy Decomposition

Reference: lamportform.tex, Section 2, equation (2) and lem:prime-energy.

For a prime `p`, the local distribution is:
  `W_p(f) = (log p) Σ_{m ≥ 1} p^{-m/2} (f(p^m) + f(p^{-m}))`

The prime energy decomposition (lem:prime-energy) expresses `-W_p(f)` as a sum
of translation norms plus a correction term proportional to `‖G‖²`.
-/

import ConnesLean.Stage2.SupportDisjointness
import ConnesLean.Stage1.ConvolutionInnerProduct
import ConnesLean.Stage1.UnitaryIdentity
import Mathlib.Data.Nat.Prime.Defs

namespace ConnesLean

open MeasureTheory Real Finset

noncomputable section

/-! ## Bounds for prime sums -/

/-- The upper bound for primes in the sum: `floor(cutoffLambda^2)`.
    Only primes `p <= cutoffLambda^2` contribute to the energy decomposition. -/
def primeBound (cutoffLambda : ℝ) : ℕ := Nat.floor (cutoffLambda ^ 2)

/-- The upper bound for exponents: `floor(2 log cutoffLambda / log p)`.
    For prime `p`, only exponents `m` with `p^m <= cutoffLambda^2` contribute,
    which is equivalent to `m <= 2 log cutoffLambda / log p`. -/
def primeExponentBound (p : ℕ) (cutoffLambda : ℝ) : ℕ :=
  Nat.floor (2 * Real.log cutoffLambda / Real.log p)

/-- The finset of primes up to `primeBound cutoffLambda`. -/
def primeFinset (cutoffLambda : ℝ) : Finset ℕ :=
  (Finset.range (primeBound cutoffLambda + 1)).filter Nat.Prime

/-- The finset of exponents `{1, ..., primeExponentBound p cutoffLambda}`. -/
def exponentFinset (p : ℕ) (cutoffLambda : ℝ) : Finset ℕ :=
  Finset.Icc 1 (primeExponentBound p cutoffLambda)

/-! ## Prime constant -/

/-- The prime constant `c_p(cutoffLambda) = -2(log p) Sum_{m=1}^{M_p} p^{-m/2}`,
    where `M_p = primeExponentBound p cutoffLambda`.

    This collects the `‖G‖²` terms from applying the unitary identity to each
    inner product `<g, U_{p^m} g>`.

    Reference: lamportform.tex, line 316. -/
def primeConstant (p : ℕ) (cutoffLambda : ℝ) : ℝ :=
  -2 * Real.log p * ∑ m ∈ exponentFinset p cutoffLambda, (p : ℝ) ^ (-(m : ℝ) / 2)

/-- The prime constant is nonpositive: `c_p(cutoffLambda) <= 0`.
    Each term in the sum is positive (p > 0, log p > 0), so the
    overall expression with the leading `-2` is nonpositive. -/
theorem primeConstant_nonpos {p : ℕ} (hp : Nat.Prime p)
    {cutoffLambda : ℝ} (_hLam : 1 < cutoffLambda) :
    primeConstant p cutoffLambda ≤ 0 := by
  unfold primeConstant
  apply mul_nonpos_of_nonpos_of_nonneg
  · apply mul_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact le_of_lt (Real.log_pos (Nat.one_lt_cast.mpr hp.one_lt))
  · apply Finset.sum_nonneg
    intro m _
    exact le_of_lt (rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) _)

/-! ## Prime energy decomposition structure -/

/-- The prime energy term for exponent `m`: the squared L² norm of the
    difference `‖G_tilde - S_{m log p} G_tilde‖²` weighted by `(log p) p^{-m/2}`.

    This is the `m`-th summand in the prime energy decomposition. -/
def primeEnergyTerm (p : ℕ) (m : ℕ) (G : ℝ → ℂ) (L : ℝ) : ENNReal :=
  ↑(Real.log p * (p : ℝ) ^ (-(m : ℝ) / 2)).toNNReal *
  ∫⁻ u, ‖zeroExtend G (logInterval L) u -
         translationOp ((m : ℝ) * Real.log p) (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ)
         ∂volume

/-- The total prime energy: sum of prime energy terms over all relevant exponents.
    `E_p(cutoffLambda, G) = Sum_{m=1}^{M_p} (log p) p^{-m/2} ‖G_tilde - S_{m log p} G_tilde‖²`. -/
def totalPrimeEnergy (p : ℕ) (cutoffLambda : ℝ) (G : ℝ → ℂ) (L : ℝ) : ENNReal :=
  ∑ m ∈ exponentFinset p cutoffLambda, primeEnergyTerm p m G L

end

end ConnesLean
