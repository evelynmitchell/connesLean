/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage 4 Property Tests

Verification tests for Stage 4 definitions and theorems covering
normal contractions and the real-to-complex bridge.
-/

import ConnesLean

open ConnesLean MeasureTheory Set Real

noncomputable section

/-! ## IsNormalContraction tests -/

/-- Absolute value is a normal contraction. -/
example : IsNormalContraction (fun x => |x|) :=
  isNormalContraction_abs

/-- The identity is a normal contraction. -/
example : IsNormalContraction id :=
  isNormalContraction_id

/-- Normal contractions are bounded: |Φ(a)| ≤ |a|. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (a : ℝ) :
    |Φ a| ≤ |a| :=
  hΦ.bound a

/-- Normal contractions are measurable. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) : Measurable Φ :=
  hΦ.measurable

/-! ## Indicator composition tests -/

/-- Indicator commutes with normal contraction composition. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (I : Set ℝ) :
    I.indicator (Φ ∘ G) = Φ ∘ (I.indicator G) :=
  indicator_comp_normalContraction hΦ G I

/-! ## liftReal tests -/

/-- liftReal applies correctly: casts to ℂ. -/
example (G : ℝ → ℝ) (u : ℝ) : liftReal G u = ↑(G u) :=
  liftReal_apply G u

/-! ## Bridge lemma tests -/

/-- zeroExtend of liftReal factors through indicator. -/
example (G : ℝ → ℝ) (I : Set ℝ) :
    zeroExtend (liftReal G) I = fun u => ↑(I.indicator G u) :=
  zeroExtend_liftReal G I

/-- zeroExtend of liftReal composed with contraction factors correctly. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (I : Set ℝ) :
    zeroExtend (liftReal (Φ ∘ G)) I = fun u => ↑(Φ (I.indicator G u)) :=
  zeroExtend_liftReal_comp hΦ G I

/-! ## Norm bridge tests -/

/-- Subtraction commutes with liftReal. -/
example (a b : ℝ → ℝ) (u : ℝ) :
    liftReal a u - liftReal b u = ↑(a u - b u) :=
  liftReal_sub_apply a b u

/-- nnnorm bridge: ℂ nnnorm = ℝ nnnorm for lifted functions. -/
example (a b : ℝ → ℝ) (u : ℝ) :
    ‖liftReal a u - liftReal b u‖₊ = ‖a u - b u‖₊ :=
  nnnorm_liftReal_sub a b u

/-- Pointwise nnnorm decrease under normal contraction. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (a b : ℝ) :
    ‖(↑(Φ a) : ℂ) - ↑(Φ b)‖₊ ≤ ‖(↑a : ℂ) - ↑b‖₊ :=
  nnnorm_comp_le hΦ a b

/-! ## Markov property tests -/

/-- Squared nnnorm decreases under contraction. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (a b : ℝ) :
    (‖(↑(Φ a) : ℂ) - ↑(Φ b)‖₊ : NNReal) ^ (2 : ℝ) ≤
    (‖(↑a : ℂ) - ↑b‖₊) ^ (2 : ℝ) :=
  nnnorm_sq_comp_le hΦ a b

/-- Pointwise nnnorm bound for zeroExtend + translationOp. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (I : Set ℝ) (t u : ℝ) :
    ‖zeroExtend (liftReal (Φ ∘ G)) I u -
      translationOp t (zeroExtend (liftReal (Φ ∘ G)) I) u‖₊ ≤
    ‖zeroExtend (liftReal G) I u -
      translationOp t (zeroExtend (liftReal G) I) u‖₊ :=
  nnnorm_zeroExtend_comp_le hΦ G I t u

/-- Integral of nnnorm² decreases under contraction. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (I : Set ℝ) (t : ℝ) :
    ∫⁻ u, ‖zeroExtend (liftReal (Φ ∘ G)) I u -
           translationOp t (zeroExtend (liftReal (Φ ∘ G)) I) u‖₊ ^ (2 : ℝ) ≤
    ∫⁻ u, ‖zeroExtend (liftReal G) I u -
           translationOp t (zeroExtend (liftReal G) I) u‖₊ ^ (2 : ℝ) :=
  lintegral_nnnorm_sq_comp_le hΦ G I t

set_option maxHeartbeats 800000 in
-- ENNReal gcongr unification is expensive
/-- Archimedean energy integrand decreases under contraction. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (L t : ℝ) :
    archEnergyIntegrand (liftReal (Φ ∘ G)) L t ≤ archEnergyIntegrand (liftReal G) L t :=
  archEnergyIntegrand_comp_le hΦ G L t

/-- Archimedean energy integral decreases under contraction. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (L : ℝ) :
    archEnergyIntegral (liftReal (Φ ∘ G)) L ≤ archEnergyIntegral (liftReal G) L :=
  archEnergyIntegral_comp_le hΦ G L

/-- Each prime energy term decreases under contraction. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (L : ℝ) (p m : ℕ) :
    primeEnergyTerm p m (liftReal (Φ ∘ G)) L ≤ primeEnergyTerm p m (liftReal G) L :=
  primeEnergyTerm_comp_le hΦ G L p m

/-- Total prime energy decreases under contraction. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (L : ℝ) (p : ℕ) (cutoffLambda : ℝ) :
    totalPrimeEnergy p cutoffLambda (liftReal (Φ ∘ G)) L ≤
    totalPrimeEnergy p cutoffLambda (liftReal G) L :=
  totalPrimeEnergy_comp_le hΦ G L p cutoffLambda

/-- Main Markov property: energy form decreases under contraction. -/
example (Φ : ℝ → ℝ) (hΦ : IsNormalContraction Φ) (G : ℝ → ℝ) (cutoffLambda : ℝ) :
    energyForm cutoffLambda (liftReal (Φ ∘ G)) ≤ energyForm cutoffLambda (liftReal G) :=
  energyForm_comp_normalContraction_le hΦ G cutoffLambda

/-- Corollary: energy of |G| ≤ energy of G. -/
example (G : ℝ → ℝ) (cutoffLambda : ℝ) :
    energyForm cutoffLambda (liftReal (fun u => |G u|)) ≤
    energyForm cutoffLambda (liftReal G) :=
  energyForm_abs_le G cutoffLambda

/-! ## Translation invariance tests -/

/-- Compact margin is positive when Icc sits strictly inside Ioo. -/
example (α β a b : ℝ) (hαa : α < a) (hbβ : b < β) :
    0 < compactMargin α β a b :=
  compactMargin_pos hαa hbβ

/-- Icc a b ⊆ Ioo α β ∩ preimage (·-t) (Ioo α β) for small t. -/
example (α β a b t : ℝ) (hαa : α < a) (hbβ : b < β)
    (ht_pos : 0 < t) (ht_bound : t < compactMargin α β a b) :
    Set.Icc a b ⊆ Set.Ioo α β ∩ Set.preimage (· - t) (Set.Ioo α β) :=
  icc_subset_ioo_inter_shift hαa hbβ ht_pos ht_bound

/-- ae shift-invariance transfers to compact subintervals. -/
example (B I : Set ℝ) (ε : ℝ) (h : IndicatorTranslationInvariant B I ε)
    (α β a b : ℝ) (hI : I = Set.Ioo α β) (hαa : α < a) (hbβ : b < β)
    (t : ℝ) (ht_pos : 0 < t) (ht_ε : t < ε) (ht_δ : t < compactMargin α β a b) :
    ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
      B.indicator (1 : ℝ → ℝ) u = B.indicator (1 : ℝ → ℝ) (u - t) :=
  indicator_ae_shift_on_compact h hI hαa hbβ ht_pos ht_ε ht_δ

/-- Quantified ae shift-invariance with explicit threshold. -/
example (B I : Set ℝ) (ε : ℝ) (h : IndicatorTranslationInvariant B I ε)
    (α β a b : ℝ) (hI : I = Set.Ioo α β) (hαa : α < a) (hbβ : b < β) :
    let δ := min ε (compactMargin α β a b)
    0 < δ ∧ ∀ t, 0 < t → t < δ →
      ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        B.indicator (1 : ℝ → ℝ) u = B.indicator (1 : ℝ → ℝ) (u - t) :=
  indicator_ae_shift_forall_small h hI hαa hbβ

end
