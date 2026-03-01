/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Norm Inequality — Proposition 10, Steps 4–7

Reference: lamportform.tex, Proposition 10, Steps 4–7 (lines 1371–1390).

For B ⊆ I with f = 1_B, g = 1_{I\B}, h = 1 (all zero-extended to I), the
pointwise inequality ‖h(u) - h(u-t)‖² ≤ ‖f(u) - f(u-t)‖² + ‖g(u) - g(u-t)‖²
holds because all values are in {0,1} with disjoint support. This propagates
through integration, weighting, and the full energy form:
  E_λ(1) ≤ E_λ(1_B) + E_λ(1_{I\B}).

## Main results

- `nnnorm_sq_indicator_le`: pointwise norm inequality for disjoint indicators
- `inner_integral_indicator_le`: integrated inequality
- `archEnergyIntegrand_indicator_le`: weighted archimedean inequality
- `primeEnergyTerm_indicator_le`: weighted prime inequality
- `energyForm_indicator_add_le`: E_λ(1) ≤ E_λ(1_B) + E_λ(1_{I\B})
-/

import ConnesLean.Stage6.ConstantInDomain

/-!
# Norm Inequality for Disjoint Indicators

Establishes that the energy of the constant function is bounded by the sum
of energies of complementary indicator functions. This is the key inequality
that, combined with the splitting equality from Stage 6C, forces cross-terms
to vanish.

Reference: lamportform.tex, Proposition 10, Steps 4–7 (lines 1371–1390).
-/

namespace ConnesLean

open MeasureTheory Set Real Filter ENNReal

noncomputable section

/-! ## Section 1: Pointwise norm inequality

For B ⊆ I, the zero-extended indicators satisfy:
  ‖h̃(u) - h̃(u-t)‖₊² ≤ ‖f̃(u) - f̃(u-t)‖₊² + ‖g̃(u) - g̃(u-t)‖₊²
where h̃ = zeroExtend 1 I, f̃ = zeroExtend (1_B) I, g̃ = zeroExtend (1_{I\B}) I.
-/

/-- **Pointwise norm inequality for disjoint indicators.**
    For B ⊆ I, at every point u and shift t:
      ‖h̃(u) - h̃(u-t)‖₊² ≤ ‖f̃(u) - f̃(u-t)‖₊² + ‖g̃(u) - g̃(u-t)‖₊²
    where h̃ = zeroExtend 1 I, f̃ = zeroExtend (1_B) I, g̃ = zeroExtend (1_{I\B}) I.

    9-case analysis on (u ∈ B, u ∈ I\B, u ∉ I) × (u-t ∈ B, u-t ∈ I\B, u-t ∉ I).
    Each case computes concrete {0,1} values.

    Reference: lamportform.tex, Proposition 10, Step 4 (line 1371). -/
theorem nnnorm_sq_indicator_le {B I : Set ℝ} (hB : B ⊆ I) (u t : ℝ) :
    (‖zeroExtend (1 : ℝ → ℂ) I u -
      zeroExtend (1 : ℝ → ℂ) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) ≤
    (‖zeroExtend (B.indicator (1 : ℝ → ℂ)) I u -
      zeroExtend (B.indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) +
    (‖zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I u -
      zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal)
        ^ (2 : ℝ) := by
  -- Simplify zero extensions via indicator_indicator
  simp only [zeroExtend_eq_indicator]
  rw [Set.indicator_indicator, Set.inter_eq_right.mpr hB,
      Set.indicator_indicator,
      show I ∩ (I \ B) = I \ B by ext x; simp [mem_inter_iff, mem_diff]]
  -- Case split on membership of u and u-t
  by_cases hu_B : u ∈ B
  · -- u ∈ B
    have hu_I : u ∈ I := hB hu_B
    have hu_ndiff : u ∉ I \ B := fun h => h.2 hu_B
    by_cases hvt_B : (u - t) ∈ B
    · -- u ∈ B, u-t ∈ B
      have hvt_I : (u - t) ∈ I := hB hvt_B
      have hvt_ndiff : (u - t) ∉ I \ B := fun h => h.2 hvt_B
      simp [Set.indicator_of_mem hu_I, Set.indicator_of_mem hu_B,
            Set.indicator_of_notMem hu_ndiff,
            Set.indicator_of_mem hvt_I, Set.indicator_of_mem hvt_B,
            Set.indicator_of_notMem hvt_ndiff]
    · by_cases hvt_diff : (u - t) ∈ I \ B
      · -- u ∈ B, u-t ∈ I\B: 0 ≤ 1 + 1
        have hvt_I : (u - t) ∈ I := hvt_diff.1
        simp [Set.indicator_of_mem hu_I, Set.indicator_of_mem hu_B,
              Set.indicator_of_notMem hu_ndiff,
              Set.indicator_of_mem hvt_I, Set.indicator_of_notMem hvt_B,
              Set.indicator_of_mem hvt_diff]
      · -- u ∈ B, u-t ∉ I: 1 ≤ 1 + 0
        have hvt_nI : (u - t) ∉ I := by
          intro h; exact hvt_B (by_contra fun hnB => hvt_diff ⟨h, hnB⟩)
        simp [Set.indicator_of_mem hu_I, Set.indicator_of_mem hu_B,
              Set.indicator_of_notMem hu_ndiff,
              Set.indicator_of_notMem hvt_nI, Set.indicator_of_notMem hvt_B,
              Set.indicator_of_notMem hvt_diff]
  · by_cases hu_diff : u ∈ I \ B
    · -- u ∈ I\B
      have hu_I : u ∈ I := hu_diff.1
      by_cases hvt_B : (u - t) ∈ B
      · -- u ∈ I\B, u-t ∈ B: 0 ≤ 1 + 1
        have hvt_I : (u - t) ∈ I := hB hvt_B
        have hvt_ndiff : (u - t) ∉ I \ B := fun h => h.2 hvt_B
        simp [Set.indicator_of_mem hu_I, Set.indicator_of_notMem hu_B,
              Set.indicator_of_mem hu_diff,
              Set.indicator_of_mem hvt_I, Set.indicator_of_mem hvt_B,
              Set.indicator_of_notMem hvt_ndiff]
      · by_cases hvt_diff : (u - t) ∈ I \ B
        · -- u ∈ I\B, u-t ∈ I\B
          have hvt_I : (u - t) ∈ I := hvt_diff.1
          simp [Set.indicator_of_mem hu_I, Set.indicator_of_notMem hu_B,
                Set.indicator_of_mem hu_diff,
                Set.indicator_of_mem hvt_I, Set.indicator_of_notMem hvt_B,
                Set.indicator_of_mem hvt_diff]
        · -- u ∈ I\B, u-t ∉ I: 1 ≤ 0 + 1
          have hvt_nI : (u - t) ∉ I := by
            intro h; exact hvt_B (by_contra fun hnB => hvt_diff ⟨h, hnB⟩)
          simp [Set.indicator_of_mem hu_I, Set.indicator_of_notMem hu_B,
                Set.indicator_of_mem hu_diff,
                Set.indicator_of_notMem hvt_nI, Set.indicator_of_notMem hvt_B,
                Set.indicator_of_notMem hvt_diff]
    · -- u ∉ I
      have hu_nI : u ∉ I := by
        intro h; exact hu_B (by_contra fun hnB => hu_diff ⟨h, hnB⟩)
      by_cases hvt_B : (u - t) ∈ B
      · -- u ∉ I, u-t ∈ B: 1 ≤ 1 + 0
        have hvt_I : (u - t) ∈ I := hB hvt_B
        have hvt_ndiff : (u - t) ∉ I \ B := fun h => h.2 hvt_B
        simp [Set.indicator_of_notMem hu_nI, Set.indicator_of_notMem hu_B,
              Set.indicator_of_notMem hu_diff,
              Set.indicator_of_mem hvt_I, Set.indicator_of_mem hvt_B,
              Set.indicator_of_notMem hvt_ndiff]
      · by_cases hvt_diff : (u - t) ∈ I \ B
        · -- u ∉ I, u-t ∈ I\B: 1 ≤ 0 + 1
          have hvt_I : (u - t) ∈ I := hvt_diff.1
          simp [Set.indicator_of_notMem hu_nI, Set.indicator_of_notMem hu_B,
                Set.indicator_of_notMem hu_diff,
                Set.indicator_of_mem hvt_I, Set.indicator_of_notMem hvt_B,
                Set.indicator_of_mem hvt_diff]
        · -- u ∉ I, u-t ∉ I
          have hvt_nI : (u - t) ∉ I := by
            intro h; exact hvt_B (by_contra fun hnB => hvt_diff ⟨h, hnB⟩)
          simp [Set.indicator_of_notMem hu_nI, Set.indicator_of_notMem hu_B,
                Set.indicator_of_notMem hu_diff,
                Set.indicator_of_notMem hvt_nI, Set.indicator_of_notMem hvt_B,
                Set.indicator_of_notMem hvt_diff]

/-! ## Section 3: Integrated inequality -/

/-- Measurability of the norm-squared integrand for zero-extended functions. -/
private theorem measurable_norm_sq_ze {G : ℝ → ℂ} {I : Set ℝ} {t : ℝ}
    (hG : Measurable G) (hI : MeasurableSet I) :
    Measurable (fun u => (‖zeroExtend G I u -
      translationOp t (zeroExtend G I) u‖₊ : ENNReal) ^ (2 : ℝ)) := by
  have hze : Measurable (zeroExtend G I) := hG.indicator hI
  exact (hze.sub (hze.comp (measurable_id.sub measurable_const)))
    |>.nnnorm.coe_nnreal_ennreal.pow_const _

/-- The integrated norm inequality: integrating the pointwise inequality gives
    `∫ ‖h̃ - S_t h̃‖² ≤ ∫ ‖f̃ - S_t f̃‖² + ∫ ‖g̃ - S_t g̃‖²`.

    Reference: lamportform.tex, Proposition 10, Step 5 (line 1378). -/
theorem inner_integral_indicator_le {B I : Set ℝ} (hB : B ⊆ I)
    (hI : MeasurableSet I) (hBm : MeasurableSet B) (t : ℝ) :
    ∫⁻ u, ‖zeroExtend (1 : ℝ → ℂ) I u -
      translationOp t (zeroExtend (1 : ℝ → ℂ) I) u‖₊ ^ (2 : ℝ) ∂volume ≤
    ∫⁻ u, ‖zeroExtend (B.indicator (1 : ℝ → ℂ)) I u -
      translationOp t (zeroExtend (B.indicator (1 : ℝ → ℂ)) I) u‖₊
        ^ (2 : ℝ) ∂volume +
    ∫⁻ u, ‖zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I u -
      translationOp t (zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I) u‖₊
        ^ (2 : ℝ) ∂volume := by
  calc ∫⁻ u, ‖zeroExtend (1 : ℝ → ℂ) I u -
          translationOp t (zeroExtend (1 : ℝ → ℂ) I) u‖₊ ^ (2 : ℝ) ∂volume
      ≤ ∫⁻ u, (‖zeroExtend (B.indicator (1 : ℝ → ℂ)) I u -
          translationOp t (zeroExtend (B.indicator (1 : ℝ → ℂ)) I) u‖₊
            ^ (2 : ℝ) +
        ‖zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I u -
          translationOp t (zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I) u‖₊
            ^ (2 : ℝ)) ∂volume := by
        apply lintegral_mono; intro u
        simp only [translationOp_apply]
        exact nnnorm_sq_indicator_le hB u t
    _ = _ := lintegral_add_left
        (measurable_norm_sq_ze (measurable_const.indicator hBm) hI) _

/-! ## Section 4: Weighted inequalities -/

/-- Archimedean energy integrand inequality: multiplying by the archimedean weight
    preserves the inequality.

    Reference: lamportform.tex, Proposition 10, Step 6 (line 1382). -/
theorem archEnergyIntegrand_indicator_le {B : Set ℝ}
    (hB : B ⊆ logInterval L)
    (hBm : MeasurableSet B) (t : ℝ) :
    archEnergyIntegrand (1 : ℝ → ℂ) L t ≤
    archEnergyIntegrand (B.indicator (1 : ℝ → ℂ)) L t +
    archEnergyIntegrand
      ((logInterval L \ B).indicator (1 : ℝ → ℂ)) L t := by
  unfold archEnergyIntegrand
  have h := inner_integral_indicator_le hB
    (measurableSet_logInterval L) hBm t
  calc _ ≤ _ * (_ + _) := mul_le_mul' le_rfl h
    _ = _ + _ := mul_add _ _ _

/-- Prime energy term inequality: multiplying by the prime weight preserves
    the inequality.

    Reference: lamportform.tex, Proposition 10, Step 6 (line 1385). -/
theorem primeEnergyTerm_indicator_le {B : Set ℝ}
    (hB : B ⊆ logInterval L) (hBm : MeasurableSet B)
    (p m : ℕ) :
    primeEnergyTerm p m (1 : ℝ → ℂ) L ≤
    primeEnergyTerm p m (B.indicator (1 : ℝ → ℂ)) L +
    primeEnergyTerm p m
      ((logInterval L \ B).indicator (1 : ℝ → ℂ)) L := by
  unfold primeEnergyTerm
  have h := inner_integral_indicator_le hB
    (measurableSet_logInterval L) hBm (↑m * Real.log ↑p)
  calc _ ≤ _ * (_ + _) := mul_le_mul' le_rfl h
    _ = _ + _ := mul_add _ _ _

/-! ## Section 5: Full energy form inequality -/

/-- **Energy form inequality:** `E_λ(1) ≤ E_λ(1_B) + E_λ(1_{I\B})`.
    Unfolds the energy form and applies the archimedean and prime inequalities.

    Combined with the splitting equality `E_λ(1) = E_λ(1_B) + E_λ(1_{I\B})`
    from Stage 6C, this forces cross-terms to vanish.

    Reference: lamportform.tex, Proposition 10, Step 7 (line 1388). -/
theorem energyForm_indicator_add_le {cutoffLambda : ℝ}
    (inv : EnergyFormSplit cutoffLambda) :
    energyForm cutoffLambda (1 : ℝ → ℂ) ≤
    energyForm cutoffLambda (inv.B.indicator (1 : ℝ → ℂ)) +
    energyForm cutoffLambda
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator
        (1 : ℝ → ℂ)) := by
  set L := Real.log cutoffLambda
  set I := logInterval L
  -- Measurability
  have hBm_ind : Measurable (inv.B.indicator (1 : ℝ → ℂ)) :=
    measurable_const.indicator inv.B_measurable
  -- Archimedean inequality
  have h_arch : archEnergyIntegral (1 : ℝ → ℂ) L ≤
      archEnergyIntegral (inv.B.indicator 1) L +
      archEnergyIntegral ((I \ inv.B).indicator 1) L := by
    unfold archEnergyIntegral
    have hBm_arch : Measurable (archEnergyIntegrand
        (inv.B.indicator (1 : ℝ → ℂ)) L) :=
      measurable_archWeight_toNNReal.coe_nnreal_ennreal.mul
        (measurable_archEnergyIntegrand hBm_ind L)
    calc ∫⁻ t in Ioo 0 (2 * L),
          archEnergyIntegrand (1 : ℝ → ℂ) L t
        ≤ ∫⁻ t in Ioo 0 (2 * L),
          (archEnergyIntegrand (inv.B.indicator 1) L t +
          archEnergyIntegrand
            ((I \ inv.B).indicator 1) L t) :=
        lintegral_mono (fun t =>
          archEnergyIntegrand_indicator_le
            inv.B_subset inv.B_measurable t)
      _ = _ := lintegral_add_left hBm_arch _
  -- Prime inequality
  have h_prime :
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda 1 L ≤
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda (inv.B.indicator 1) L +
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda
          ((I \ inv.B).indicator 1) L := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro p _
    unfold totalPrimeEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro m _
    exact primeEnergyTerm_indicator_le
      inv.B_subset inv.B_measurable p m
  -- Combine: E(1) = arch + prime ≤ (archB + archD) + (primeB + primeD)
  --                              = (archB + primeB) + (archD + primeD) = E(B) + E(D)
  unfold energyForm
  calc archEnergyIntegral 1 L +
        ∑ p ∈ primeFinset cutoffLambda,
          totalPrimeEnergy p cutoffLambda 1 L
      ≤ (archEnergyIntegral (inv.B.indicator 1) L +
          archEnergyIntegral ((I \ inv.B).indicator 1) L) +
        (∑ p ∈ primeFinset cutoffLambda,
          totalPrimeEnergy p cutoffLambda (inv.B.indicator 1) L +
        ∑ p ∈ primeFinset cutoffLambda,
          totalPrimeEnergy p cutoffLambda
            ((I \ inv.B).indicator 1) L) :=
        add_le_add h_arch h_prime
    _ = _ := add_add_add_comm _ _ _ _

/-! ## Section 6: Soundness tests -/

-- Test 1: energyForm_indicator_add_le composes with EnergyFormSplit
example {cutoffLambda : ℝ}
    (inv : EnergyFormSplit cutoffLambda) :
    energyForm cutoffLambda (1 : ℝ → ℂ) ≤
    energyForm cutoffLambda (inv.B.indicator (1 : ℝ → ℂ)) +
    energyForm cutoffLambda
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator
        (1 : ℝ → ℂ)) :=
  energyForm_indicator_add_le inv

-- Test 2: splitting equality composes
example {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    energyForm cutoffLambda (1 : ℝ → ℂ) =
    energyForm cutoffLambda (inv.B.indicator (1 : ℝ → ℂ)) +
    energyForm cutoffLambda
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator
        (1 : ℝ → ℂ)) :=
  (splitting_applied_to_constant hLam inv).2.2

-- Test 3: pointwise inequality at specific point composes
example {B I : Set ℝ} (hB : B ⊆ I) :
    ∀ u t, (‖zeroExtend (1 : ℝ → ℂ) I u -
      zeroExtend (1 : ℝ → ℂ) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) ≤
    (‖zeroExtend (B.indicator (1 : ℝ → ℂ)) I u -
      zeroExtend (B.indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) +
    (‖zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I u -
      zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal)
        ^ (2 : ℝ) :=
  fun u t => nnnorm_sq_indicator_le hB u t

end

end ConnesLean
