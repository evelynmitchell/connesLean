/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convention Notes for the Formalization

## Inner Product Convention
The paper uses `⟨g, h⟩ = ∫ g(y) conj(h(y)) d*y`, which is conjugate-linear in h
(second argument). Mathlib's `inner` is conjugate-linear in the first argument:
`⟪x, y⟫_𝕜` is linear in `y`.

Correspondence: paper's `⟨g, h⟩ = ⟪h, g⟫_Mathlib = conj(⟪g, h⟫_Mathlib)`.

For real parts: `Re(paper's ⟨g,h⟩) = Re(⟪g, h⟫_Mathlib)` since `Re(z) = Re(conj z)`.

## Measure Convention
The multiplicative Haar measure `d*x = dx/x` on `R_+* = (0,∞)` is realized as
the pushforward of Lebesgue measure under `exp : ℝ → R_+*`.
-/

import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Notation and Conventions

Documents the inner product and measure conventions used in the formalization of the
restricted Weil quadratic form.

* **Inner product**: The paper uses `⟨g, h⟩ = ∫ g(y) conj(h(y)) d*y` (conjugate-linear in h).
  Mathlib's `inner` is conjugate-linear in the first argument, so
  paper's `⟨g, h⟩ = ⟪h, g⟫_Mathlib = conj(⟪g, h⟫_Mathlib)`.
  For real parts: `Re(paper's ⟨g,h⟩) = Re(⟪g, h⟫_Mathlib)`.
* **Measure**: The multiplicative Haar measure `d*x = dx/x` on `ℝ₊*` is realized as
  the pushforward of Lebesgue measure under `exp : ℝ → ℝ₊*`.
-/

namespace ConnesLean

-- This file serves as documentation of conventions.
-- No definitions are placed here; each Stage1 file imports Mathlib directly.

end ConnesLean
