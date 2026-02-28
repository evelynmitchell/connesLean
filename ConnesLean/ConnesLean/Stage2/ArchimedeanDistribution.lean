/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Archimedean Distribution W_R(f)

Reference: lamportform.tex, Section 2, equation (3).

The archimedean distribution is:
  `W_R(f) = (log 4π + γ) f(1) + ∫_{(0,∞)} (f(e^t) + f(e^{-t}) - 2 e^{-t/2} f(1)) w(t) dt`
where `w(t) = exp(t/2) / (2 sinh t)` is the archimedean weight.

In additive (log) coordinates with `x = e^t`, this becomes:
  `W_R(f) = (log 4π + γ) f(1) + ∫_{(0,∞)} (f(expToRPos t) + f(expToRPos(-t))
                                         - 2 exp(-t/2) f(1)) w(t) dt`
-/

import ConnesLean.Stage2.ArchimedeanWeight

/-!
# Archimedean Distribution W_R(f)

Defines the archimedean distribution combining the logarithmic constant term and
weighted integral of shifted function differences:
  `W_R(f) = (log 4π + γ) f(1) + ∫₀^∞ (f(eᵗ) + f(e⁻ᵗ) - 2 e⁻ᵗ/² f(1)) w(t) dt`

Reference: lamportform.tex, Section 2, equation (3).
-/

namespace ConnesLean

open MeasureTheory Real Set

noncomputable section

/-! ## Auxiliary: exponential negation -/

/-- `expToRPos (-t)` equals `(expToRPos t)⁻¹`: negating the additive coordinate
    corresponds to inversion in the multiplicative group `R_+*`. -/
@[simp]
theorem expToRPos_neg (t : ℝ) : expToRPos (-t) = (expToRPos t)⁻¹ := by
  ext; simp [expToRPos, RPos.inv_val, Real.exp_neg]

/-! ## The archimedean distribution -/

/-- The archimedean distribution `W_R(f)` from equation (3) of lamportform.tex.

    For `f : RPos → ℂ`, this is:
      `W_R(f) = (log 4π + γ) f(1) + ∫_{(0,∞)} (f(e^t) + f(e^{-t}) - 2 e^{-t/2} f(1)) w(t) dt`

    The Bochner integral returns 0 for non-integrable integrands, so this definition
    is total. It is meaningful when `f` has compact support in `RPos`.

    Reference: lamportform.tex, equation (3), Section 2. -/
def archDistribution (f : RPos → ℂ) : ℂ :=
  ↑(Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) * f 1 +
  ∫ t in Ioi (0 : ℝ),
    (f (expToRPos t) + f (expToRPos (-t)) -
     2 * ↑(Real.exp (-t / 2)) * f 1) * ↑(archWeight t)

/-! ## Properties of the archimedean distribution -/

/-- The archimedean distribution of the zero function is zero. -/
theorem archDistribution_zero : archDistribution 0 = 0 := by
  simp [archDistribution]

/-- The archimedean distribution at a constant function `f(x) = c` equals
    `(log 4π + γ) c + ∫_{(0,∞)} (2 - 2 exp(-t/2)) w(t) dt · c`.
    In particular the singular part `(log 4π + γ) c` is explicitly visible. -/
theorem archDistribution_const (c : ℂ) :
    archDistribution (fun _ => c) =
    ↑(Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) * c +
    ∫ t in Ioi (0 : ℝ),
      (2 - 2 * ↑(Real.exp (-t / 2))) * ↑(archWeight t) * c := by
  unfold archDistribution
  congr 1
  congr 1 with t
  ring

end

end ConnesLean
