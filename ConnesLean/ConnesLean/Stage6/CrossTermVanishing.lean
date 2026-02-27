/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cross-Term Vanishing — Proposition 10, Steps 4–9

Reference: lamportform.tex, Proposition 10 (lines 1351–1425).

Proves that the cross-product of the indicator projections vanishes
under all translations, so that 1_B is translation-invariant a.e. on
the overlap I ∩ (I+t).

This is the penultimate step in the irreducibility chain
(6A → 6B → 6C → **6D** → 6E).

## Main results

- `indicator_invariant_of_ideal`: 1_B(u) = 1_B(u−t) a.e. on I ∩ (I+t)
-/

import ConnesLean.Stage6.ConstantInDomain
import ConnesLean.Stage6.IndicatorEnergy

namespace ConnesLean

open MeasureTheory Real Finset Set ENNReal

noncomputable section

/-! ## Cross-indicator definition -/

/-- ENNReal indicator: 1 when u ∈ B∩I and u-t ∈ I\B. -/
def crossIndicator (B : Set ℝ) (L t : ℝ) (u : ℝ) : ENNReal :=
  (logInterval L ∩ B).indicator (1 : ℝ → ENNReal) u *
  ((· - t) ⁻¹' (logInterval L \ B)).indicator (1 : ℝ → ENNReal) u

private theorem measurable_crossIndicator {B : Set ℝ}
    (hB : MeasurableSet B) (L t : ℝ) :
    Measurable (crossIndicator B L t) := by
  unfold crossIndicator
  exact (Measurable.indicator measurable_const
    ((measurableSet_logInterval L).inter hB)).mul
    (Measurable.indicator measurable_const
      (((measurableSet_logInterval L).diff hB).preimage
        (measurable_id.sub measurable_const)))

/-! ## Abbreviations -/

private abbrev f_tilde (B : Set ℝ) (L : ℝ) : ℝ → ℂ :=
  zeroExtend (B.indicator (fun _ => (1 : ℂ))) (logInterval L)

private abbrev g_tilde (B : Set ℝ) (L : ℝ) : ℝ → ℂ :=
  zeroExtend ((logInterval L \ B).indicator (fun _ => (1 : ℂ)))
    (logInterval L)

private abbrev h_tilde (L : ℝ) : ℝ → ℂ :=
  zeroExtend (fun _ => (1 : ℂ)) (logInterval L)

private abbrev innerInt (φ : ℝ → ℂ) (t : ℝ) : ENNReal :=
  ∫⁻ u, (‖φ u - translationOp t φ u‖₊ : ENNReal) ^ (2 : ℝ) ∂volume

/-! ## Measurability helpers -/

private theorem measurable_f_tilde {B : Set ℝ}
    (hB_meas : MeasurableSet B) (L : ℝ) :
    Measurable (f_tilde B L) :=
  (measurable_const.indicator hB_meas).indicator
    (measurableSet_logInterval L)

private theorem measurable_g_tilde {B : Set ℝ}
    (hB_meas : MeasurableSet B) (L : ℝ) :
    Measurable (g_tilde B L) :=
  (measurable_const.indicator
    ((measurableSet_logInterval L).diff hB_meas)).indicator
    (measurableSet_logInterval L)

private theorem measurable_h_tilde (L : ℝ) :
    Measurable (h_tilde L) :=
  measurable_const.indicator (measurableSet_logInterval L)

private theorem measurable_inner_integrand
    {φ : ℝ → ℂ} (hφ : Measurable φ) (t : ℝ) :
    Measurable (fun u =>
      (‖φ u - translationOp t φ u‖₊ : ENNReal) ^ (2 : ℝ)) :=
  (((hφ.sub (hφ.comp (measurable_id.sub measurable_const))).nnnorm).coe_nnreal_ennreal).pow_const _

private theorem measurable_archWeight_ennreal' :
    Measurable (fun t => (archWeight t).toNNReal : ℝ → NNReal) :=
  measurable_real_toNNReal.comp
    ((Real.continuous_exp.measurable.comp
      (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh))

private theorem measurable_archEnergyIntegrand_full
    {G : ℝ → ℂ} (hG : Measurable G) (L : ℝ) :
    Measurable (archEnergyIntegrand G L) := by
  unfold archEnergyIntegrand
  exact (measurable_coe_nnreal_ennreal.comp
    measurable_archWeight_ennreal').mul
    (measurable_archEnergyIntegrand hG L)

/-! ## Step 4: Pointwise norm inequality -/

/-- Pointwise: ‖h̃ diff‖² ≤ ‖f̃ diff‖² + ‖g̃ diff‖². -/
private theorem nnnorm_sq_indicator_ge
    {B : Set ℝ} (_hB : B ⊆ logInterval L) (t : ℝ) (u : ℝ) :
    (‖h_tilde L u - translationOp t (h_tilde L) u‖₊ :
      ENNReal) ^ (2 : ℝ) ≤
    (‖f_tilde B L u - translationOp t
      (f_tilde B L) u‖₊ : ENNReal) ^ (2 : ℝ) +
    (‖g_tilde B L u - translationOp t
      (g_tilde B L) u‖₊ : ENNReal) ^ (2 : ℝ) := by
  simp only [f_tilde, g_tilde, h_tilde, translationOp_apply, zeroExtend]
  by_cases hI_u : u ∈ logInterval L
  · by_cases hI_ut : (u - t) ∈ logInterval L
    · -- u ∈ I, u-t ∈ I
      by_cases hB_u : u ∈ B
      · by_cases hB_ut : (u - t) ∈ B
        · -- u ∈ B∩I, u-t ∈ B∩I: all diffs cancel
          have h1 : u - t ∉ logInterval L \ B := fun h => h.2 hB_ut
          simp only [indicator_of_mem hI_u, indicator_of_mem hI_ut,
            indicator_of_mem hB_u, indicator_of_mem hB_ut,
            indicator_of_notMem (show u ∉ logInterval L \ B
              from fun h => h.2 hB_u),
            indicator_of_notMem h1,
            sub_self, nnnorm_zero, ENNReal.coe_zero,
            zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
          exact le_self_add
        · -- u ∈ B∩I, u-t ∈ I\B: cross case, LHS=0 ≤ 2=RHS
          have h1 : u - t ∈ logInterval L \ B := ⟨hI_ut, hB_ut⟩
          simp only [indicator_of_mem hI_u, indicator_of_mem hI_ut,
            indicator_of_mem hB_u, indicator_of_notMem hB_ut,
            indicator_of_notMem (show u ∉ logInterval L \ B
              from fun h => h.2 hB_u),
            indicator_of_mem h1, sub_self, sub_zero, zero_sub,
            nnnorm_zero, nnnorm_one, nnnorm_neg,
            ENNReal.coe_zero, ENNReal.coe_one,
            zero_rpow_of_pos (by norm_num : (0:ℝ) < 2),
            ENNReal.one_rpow]
          norm_num
      · by_cases hB_ut : (u - t) ∈ B
        · -- u ∈ I\B, u-t ∈ B∩I: other cross case
          have h1 : u ∈ logInterval L \ B := ⟨hI_u, hB_u⟩
          have h2 : u - t ∉ logInterval L \ B := fun h => h.2 hB_ut
          simp only [indicator_of_mem hI_u, indicator_of_mem hI_ut,
            indicator_of_notMem hB_u, indicator_of_mem hB_ut,
            indicator_of_mem h1, indicator_of_notMem h2,
            sub_self, sub_zero, zero_sub,
            nnnorm_zero, nnnorm_one, nnnorm_neg,
            ENNReal.coe_zero, ENNReal.coe_one,
            zero_rpow_of_pos (by norm_num : (0:ℝ) < 2),
            ENNReal.one_rpow]
          norm_num
        · -- u ∈ I\B, u-t ∈ I\B: all diffs cancel
          have h1 : u ∈ logInterval L \ B := ⟨hI_u, hB_u⟩
          have h2 : u - t ∈ logInterval L \ B := ⟨hI_ut, hB_ut⟩
          simp only [indicator_of_mem hI_u, indicator_of_mem hI_ut,
            indicator_of_notMem hB_u, indicator_of_notMem hB_ut,
            indicator_of_mem h1, indicator_of_mem h2,
            sub_self, nnnorm_zero, ENNReal.coe_zero,
            zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
          exact le_self_add
    · -- u ∈ I, u-t ∉ I: LHS = 1, RHS = 1
      by_cases hB_u : u ∈ B
      · simp only [indicator_of_mem hI_u, indicator_of_notMem hI_ut,
          indicator_of_mem hB_u,
          indicator_of_notMem (show u ∉ logInterval L \ B
            from fun h => h.2 hB_u),
          sub_zero, nnnorm_one, nnnorm_zero, ENNReal.coe_one, ENNReal.coe_zero,
          zero_rpow_of_pos (by norm_num : (0:ℝ) < 2),
          ENNReal.one_rpow]
        norm_num
      · have h1 : u ∈ logInterval L \ B := ⟨hI_u, hB_u⟩
        simp only [indicator_of_mem hI_u, indicator_of_notMem hI_ut,
          indicator_of_notMem hB_u, indicator_of_mem h1,
          sub_zero, nnnorm_one, nnnorm_zero, ENNReal.coe_one, ENNReal.coe_zero,
          zero_rpow_of_pos (by norm_num : (0:ℝ) < 2),
          ENNReal.one_rpow]
        norm_num
  · -- u ∉ I (hence u ∉ B)
    by_cases hI_ut : (u - t) ∈ logInterval L
    · by_cases hB_ut : (u - t) ∈ B
      · -- u ∉ I, u-t ∈ B∩I
        have h1 : u - t ∉ logInterval L \ B := fun h => h.2 hB_ut
        simp only [indicator_of_notMem hI_u, indicator_of_mem hI_ut,
          indicator_of_mem hB_ut, indicator_of_notMem h1,
          zero_sub, nnnorm_neg, nnnorm_one, nnnorm_zero,
          ENNReal.coe_one, ENNReal.coe_zero,
          zero_rpow_of_pos (by norm_num : (0:ℝ) < 2),
          ENNReal.one_rpow]
        norm_num
      · -- u ∉ I, u-t ∈ I\B
        have h1 : u - t ∈ logInterval L \ B := ⟨hI_ut, hB_ut⟩
        simp only [indicator_of_notMem hI_u, indicator_of_mem hI_ut,
          indicator_of_notMem hB_ut, indicator_of_mem h1,
          zero_sub, nnnorm_neg, nnnorm_one, nnnorm_zero,
          ENNReal.coe_one, ENNReal.coe_zero,
          zero_rpow_of_pos (by norm_num : (0:ℝ) < 2),
          ENNReal.one_rpow]
        norm_num
    · -- u ∉ I, u-t ∉ I: all 0
      simp only [indicator_of_notMem hI_u, indicator_of_notMem hI_ut,
        sub_self, nnnorm_zero, ENNReal.coe_zero,
        zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
      exact le_self_add

/-! ## Step 5: Inner integral inequality -/

private theorem inner_integral_indicator_ge
    {B : Set ℝ} (hB : B ⊆ logInterval L)
    (hB_meas : MeasurableSet B) (t : ℝ) :
    innerInt (h_tilde L) t ≤
    innerInt (f_tilde B L) t + innerInt (g_tilde B L) t :=
  calc innerInt (h_tilde L) t
      ≤ ∫⁻ u, ((‖f_tilde B L u - translationOp t
          (f_tilde B L) u‖₊ : ENNReal) ^ (2 : ℝ) +
         (‖g_tilde B L u - translationOp t
          (g_tilde B L) u‖₊ : ENNReal) ^ (2 : ℝ))
        ∂volume :=
        lintegral_mono (nnnorm_sq_indicator_ge hB t)
    _ = _ := lintegral_add_left
        (measurable_inner_integrand
          (measurable_f_tilde hB_meas L) t) _

/-! ## Step 6: Weighted inequality -/

private theorem archEnergyIntegrand_indicator_ge
    {B : Set ℝ} (hB : B ⊆ logInterval L)
    (hB_meas : MeasurableSet B) (t : ℝ) :
    archEnergyIntegrand (fun _ => (1 : ℂ)) L t ≤
    archEnergyIntegrand (B.indicator (fun _ => (1 : ℂ))) L t +
    archEnergyIntegrand
      ((logInterval L \ B).indicator (fun _ => (1 : ℂ))) L t := by
  unfold archEnergyIntegrand
  calc _ ≤ _ := mul_le_mul_right
        (inner_integral_indicator_ge hB hB_meas t) _
    _ = _ := mul_add _ _ _

/-! ## Helper: ENNReal cancellation -/

/-- If a + b = c + d and a ≤ c and b ≤ d with b ≠ ⊤, then a = c. -/
private theorem ennreal_cancel {a b c d : ENNReal}
    (h_eq : a + b = c + d)
    (ha : a ≤ c) (hb : b ≤ d) (hb_ne : b ≠ ⊤) : a = c := by
  have h1 : c + b ≤ c + d := by gcongr
  have h2 : a + b ≤ c + b := by gcongr
  exact WithTop.add_right_cancel hb_ne (le_antisymm h2 (h_eq ▸ h1))

/-! ## Step 7: Energy form inequality -/

private theorem energyForm_indicator_add_ge
    {cutoffLambda : ℝ} {B : Set ℝ}
    (hB_meas : MeasurableSet B)
    (hB : B ⊆ logInterval (Real.log cutoffLambda)) :
    energyForm cutoffLambda (fun _ => (1 : ℂ)) ≤
    energyForm cutoffLambda (B.indicator (fun _ => (1 : ℂ))) +
    energyForm cutoffLambda
      ((logInterval (Real.log cutoffLambda) \ B).indicator
        (fun _ => (1 : ℂ))) := by
  set L := Real.log cutoffLambda
  unfold energyForm
  -- Arch inequality
  have h_arch :
      archEnergyIntegral (fun _ => (1 : ℂ)) L ≤
      archEnergyIntegral (B.indicator (fun _ => (1 : ℂ))) L +
      archEnergyIntegral
        ((logInterval L \ B).indicator (fun _ => (1 : ℂ))) L := by
    unfold archEnergyIntegral
    calc ∫⁻ t in Ioo 0 (2 * L),
          archEnergyIntegrand (fun _ => (1 : ℂ)) L t ∂volume
        ≤ ∫⁻ t in Ioo 0 (2 * L),
          (archEnergyIntegrand
            (B.indicator (fun _ => (1 : ℂ))) L t +
           archEnergyIntegrand
            ((logInterval L \ B).indicator
              (fun _ => (1 : ℂ))) L t) ∂volume :=
          setLIntegral_mono
            ((measurable_archEnergyIntegrand_full
              (measurable_const.indicator hB_meas) L).add
             (measurable_archEnergyIntegrand_full
              (measurable_const.indicator
                ((measurableSet_logInterval L).diff hB_meas)) L))
            (fun t _ =>
              archEnergyIntegrand_indicator_ge hB hB_meas t)
      _ = _ := lintegral_add_left
          (measurable_archEnergyIntegrand_full
            (measurable_const.indicator hB_meas) L) _
  -- Prime inequality
  have h_prime :
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda (fun _ => (1 : ℂ)) L ≤
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda
          (B.indicator (fun _ => (1 : ℂ))) L +
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda
          ((logInterval L \ B).indicator
            (fun _ => (1 : ℂ))) L := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro p _
    unfold totalPrimeEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro m _
    unfold primeEnergyTerm
    calc _ ≤ _ := mul_le_mul_right
          (inner_integral_indicator_ge hB hB_meas _) _
      _ = _ := mul_add _ _ _
  calc _ ≤ _ := add_le_add h_arch h_prime
    _ = _ := (add_add_add_comm _ _ _ _).symm

/-! ## Step 8: Archimedean energy equality -/

private theorem archEnergyIntegral_indicator_eq
    (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) :
    archEnergyIntegral
      (ideal.B.indicator (fun _ => (1 : ℂ)))
      (Real.log cutoffLambda) +
    archEnergyIntegral
      ((logInterval (Real.log cutoffLambda) \ ideal.B).indicator
        (fun _ => (1 : ℂ)))
      (Real.log cutoffLambda) =
    archEnergyIntegral (fun _ => (1 : ℂ))
      (Real.log cutoffLambda) := by
  set L := Real.log cutoffLambda
  -- Total energy splitting from 6C
  have h_split := splitting_applied_to_constant cutoffLambda hLam ideal
  -- Finiteness
  have h_fin := constant_in_formDomain cutoffLambda
  have h_ne : energyForm cutoffLambda (fun _ => (1 : ℂ)) ≠ ⊤ := h_fin
  -- Unfold energyForm in h_split and rearrange
  simp only [energyForm] at h_split
  -- h_split: arch_h + prime_h = (arch_f + prime_f) + (arch_g + prime_g)
  -- Rearrange RHS: (arch_f + arch_g) + (prime_f + prime_g)
  rw [add_add_add_comm] at h_split
  -- Arch inequality
  have h_arch_le :
      archEnergyIntegral (fun _ => (1 : ℂ)) L ≤
      archEnergyIntegral
        (ideal.B.indicator (fun _ => (1 : ℂ))) L +
      archEnergyIntegral
        ((logInterval L \ ideal.B).indicator
          (fun _ => (1 : ℂ))) L := by
    unfold archEnergyIntegral
    calc ∫⁻ t in Ioo 0 (2 * L),
          archEnergyIntegrand (fun _ => (1 : ℂ)) L t ∂volume
        ≤ ∫⁻ t in Ioo 0 (2 * L),
          (archEnergyIntegrand
            (ideal.B.indicator (fun _ => (1 : ℂ))) L t +
           archEnergyIntegrand
            ((logInterval L \ ideal.B).indicator
              (fun _ => (1 : ℂ))) L t) ∂volume :=
          setLIntegral_mono
            ((measurable_archEnergyIntegrand_full
              (measurable_const.indicator ideal.B_measurable)
                L).add
             (measurable_archEnergyIntegrand_full
              (measurable_const.indicator
                ((measurableSet_logInterval L).diff
                  ideal.B_measurable)) L))
            (fun t _ =>
              archEnergyIntegrand_indicator_ge
                ideal.B_subset ideal.B_measurable t)
      _ = _ := lintegral_add_left
          (measurable_archEnergyIntegrand_full
            (measurable_const.indicator ideal.B_measurable) L) _
  -- Prime inequality
  have h_prime_le :
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda (fun _ => (1 : ℂ)) L ≤
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda
          (ideal.B.indicator (fun _ => (1 : ℂ))) L +
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda
          ((logInterval L \ ideal.B).indicator
            (fun _ => (1 : ℂ))) L := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro p _
    unfold totalPrimeEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro m _
    unfold primeEnergyTerm
    calc _ ≤ _ := mul_le_mul_right
          (inner_integral_indicator_ge ideal.B_subset
            ideal.B_measurable _) _
      _ = _ := mul_add _ _ _
  -- Finiteness of prime sum
  have h_prime_ne : ∑ p ∈ primeFinset cutoffLambda,
      totalPrimeEnergy p cutoffLambda (fun _ => (1 : ℂ)) L ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mp (by
        change energyForm cutoffLambda (fun _ => (1 : ℂ)) ≠ ⊤
        exact h_fin)).2
      le_rfl
  -- Extract arch equality by cancellation
  exact (ennreal_cancel h_split h_arch_le h_prime_le h_prime_ne).symm

/-! ## Step 9: a.e. equality of archEnergyIntegrand -/

private theorem archEnergyIntegrand_indicator_ae_eq
    (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) :
    ∀ᵐ t ∂(volume.restrict
      (Ioo 0 (2 * Real.log cutoffLambda))),
    archEnergyIntegrand
      (ideal.B.indicator (fun _ => (1 : ℂ)))
      (Real.log cutoffLambda) t +
    archEnergyIntegrand
      ((logInterval (Real.log cutoffLambda) \ ideal.B).indicator (fun _ => (1 : ℂ)))
      (Real.log cutoffLambda) t =
    archEnergyIntegrand (fun _ => (1 : ℂ))
      (Real.log cutoffLambda) t := by
  set L := Real.log cutoffLambda
  -- Pointwise inequality (a.e.)
  have h_ae_le :
      (fun t => archEnergyIntegrand (fun _ => (1 : ℂ)) L t) ≤ᵐ[volume.restrict (Ioo 0 (2 * L))]
      (fun t => archEnergyIntegrand
        (ideal.B.indicator (fun _ => (1 : ℂ))) L t +
       archEnergyIntegrand
        ((logInterval L \ ideal.B).indicator
          (fun _ => (1 : ℂ))) L t) :=
    Filter.Eventually.of_forall (fun t =>
      archEnergyIntegrand_indicator_ge
        ideal.B_subset ideal.B_measurable t)
  -- Finiteness
  have h_lhs_ne_top :
      ∫⁻ t in Ioo 0 (2 * L),
        archEnergyIntegrand (fun _ => (1 : ℂ)) L t ∂volume ≠ ⊤ := by
    have hE := constant_in_formDomain cutoffLambda
    change energyForm cutoffLambda (fun _ => 1) ≠ ⊤ at hE
    unfold energyForm archEnergyIntegral at hE
    exact ne_top_of_le_ne_top hE le_self_add
  -- RHS measurability
  have h_rhs_meas : AEMeasurable (fun t =>
      archEnergyIntegrand
        (ideal.B.indicator (fun _ => (1 : ℂ))) L t +
      archEnergyIntegrand
        ((logInterval L \ ideal.B).indicator
          (fun _ => (1 : ℂ))) L t)
      (volume.restrict (Ioo 0 (2 * L))) :=
    ((measurable_archEnergyIntegrand_full
      (measurable_const.indicator ideal.B_measurable) L).add
      (measurable_archEnergyIntegrand_full
        (measurable_const.indicator
          ((measurableSet_logInterval L).diff
            ideal.B_measurable)) L)).aemeasurable
  -- Integral equality
  have h_int_eq :=
    archEnergyIntegral_indicator_eq cutoffLambda hLam ideal
  have h_int_le :
      ∫⁻ t in Ioo 0 (2 * L),
        (archEnergyIntegrand
          (ideal.B.indicator (fun _ => (1 : ℂ))) L t +
         archEnergyIntegrand
          ((logInterval L \ ideal.B).indicator
            (fun _ => (1 : ℂ))) L t) ∂volume ≤
      ∫⁻ t in Ioo 0 (2 * L),
        archEnergyIntegrand (fun _ => (1 : ℂ)) L t ∂volume := by
    unfold archEnergyIntegral at h_int_eq
    rw [← h_int_eq]
    exact (lintegral_add_left
      (measurable_archEnergyIntegrand_full
        (measurable_const.indicator ideal.B_measurable) L) _).le
  have h_ae_eq := ae_eq_of_ae_le_of_lintegral_le
    h_ae_le h_lhs_ne_top h_rhs_meas h_int_le
  filter_upwards [h_ae_eq] with t ht
  exact ht.symm

/-! ## Step 10: Inner integral equality a.e. -/

private theorem inner_integral_indicator_ae_eq
    (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) :
    ∀ᵐ t ∂(volume.restrict
      (Ioo 0 (2 * Real.log cutoffLambda))),
    innerInt (f_tilde ideal.B (Real.log cutoffLambda)) t +
    innerInt (g_tilde ideal.B (Real.log cutoffLambda)) t =
    innerInt (h_tilde (Real.log cutoffLambda)) t := by
  set L := Real.log cutoffLambda
  filter_upwards [
    archEnergyIntegrand_indicator_ae_eq
      cutoffLambda hLam ideal,
    ae_restrict_mem measurableSet_Ioo]
    with t ht ht_mem
  -- ht: weight * innerInt_f + weight * innerInt_g = weight * innerInt_h
  unfold archEnergyIntegrand at ht
  rw [← mul_add] at ht
  have hw_ne : (↑(archWeight t).toNNReal : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (by
      rw [ne_eq, Real.toNNReal_eq_zero]; push_neg
      exact archWeight_pos ht_mem.1)
  exact (ENNReal.mul_right_inj hw_ne ENNReal.coe_ne_top).mp ht

/-! ## Step 11: Inner integral continuity -/

private theorem inner_integral_indicator_continuous
    {B : Set ℝ} (hB_meas : MeasurableSet B) (L : ℝ) :
    Continuous (fun t => innerInt (f_tilde B L) t) := by
  apply translation_norm_sq_continuous
  · exact measurable_f_tilde hB_meas L
  · calc ∫⁻ u, ‖f_tilde B L u‖₊ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ u, (logInterval L).indicator 1 u ∂volume := by
          apply lintegral_mono; intro u
          simp only [f_tilde, zeroExtend, Set.indicator]
          split_ifs <;> simp [nnnorm_one]
      _ = volume (logInterval L) :=
          lintegral_indicator_one (measurableSet_logInterval L)
      _ < ⊤ := measure_Ioo_lt_top

private theorem inner_integral_constant_continuous (L : ℝ) :
    Continuous (fun t => innerInt (h_tilde L) t) := by
  apply translation_norm_sq_continuous
  · exact measurable_h_tilde L
  · calc ∫⁻ u, ‖h_tilde L u‖₊ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ u, (logInterval L).indicator 1 u ∂volume := by
          apply lintegral_mono; intro u
          simp only [h_tilde, zeroExtend, Set.indicator]
          split_ifs <;> simp [nnnorm_one]
      _ = volume (logInterval L) :=
          lintegral_indicator_one (measurableSet_logInterval L)
      _ < ⊤ := measure_Ioo_lt_top

/-! ## Step 12: Cross difference continuity -/

private theorem innerInt_h_ne_top (L : ℝ) (t : ℝ) :
    innerInt (h_tilde L) t ≠ ⊤ := by
  apply ne_of_lt
  have hI_meas := measurableSet_logInterval L
  have hIt_meas : MeasurableSet ((· - t) ⁻¹' logInterval L) :=
    hI_meas.preimage (measurable_id.sub measurable_const)
  set U := logInterval L ∪ (· - t) ⁻¹' logInterval L
  have hU_meas : MeasurableSet U := hI_meas.union hIt_meas
  calc innerInt (h_tilde L) t
      ≤ ∫⁻ u, U.indicator (1 : ℝ → ENNReal) u ∂volume := by
        apply lintegral_mono; intro u
        simp only [h_tilde, translationOp_apply, zeroExtend]
        by_cases hI : u ∈ logInterval L <;> by_cases hIt : (u - t) ∈ logInterval L
        · -- u ∈ I, u-t ∈ I: integrand = 0
          simp only [indicator_of_mem hI, indicator_of_mem hIt,
            sub_self, nnnorm_zero, ENNReal.coe_zero,
            zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
          exact zero_le _
        · -- u ∈ I, u-t ∉ I: integrand = 1
          simp only [indicator_of_mem hI, indicator_of_notMem hIt,
            sub_zero, nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow]
          rw [indicator_of_mem (show u ∈ U from Set.mem_union_left _ hI)]
          simp
        · -- u ∉ I, u-t ∈ I: integrand = 1
          simp only [indicator_of_notMem hI, indicator_of_mem hIt,
            zero_sub, nnnorm_neg, nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow]
          rw [indicator_of_mem (show u ∈ U from Set.mem_union_right _
            (show u ∈ (· - t) ⁻¹' logInterval L from hIt))]
          simp
        · -- u ∉ I, u-t ∉ I: integrand = 0
          simp only [indicator_of_notMem hI, indicator_of_notMem hIt,
            sub_self, nnnorm_zero, ENNReal.coe_zero,
            zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
          exact zero_le _
    _ = volume U := lintegral_indicator_one hU_meas
    _ ≤ volume (logInterval L) + volume ((· - t) ⁻¹' logInterval L) :=
        measure_union_le _ _
    _ < ⊤ := by
        apply ENNReal.add_lt_top.mpr; constructor
        · exact measure_Ioo_lt_top
        · rw [show (· - t) ⁻¹' logInterval L = Set.Ioo (-L + t) (L + t) from by
            ext u; simp [logInterval, Set.mem_Ioo]]
          exact measure_Ioo_lt_top

private theorem crossDiff_continuous {B : Set ℝ}
    (hB_meas : MeasurableSet B) {L : ℝ} :
    Continuous (fun t =>
      (innerInt (f_tilde B L) t +
       innerInt (g_tilde B L) t) -
       innerInt (h_tilde L) t) := by
  have hF : Continuous (fun t =>
      innerInt (f_tilde B L) t +
      innerInt (g_tilde B L) t) :=
    Continuous.add
      (inner_integral_indicator_continuous hB_meas L)
      (inner_integral_indicator_continuous
        ((measurableSet_logInterval L).diff hB_meas) L)
  have hG := inner_integral_constant_continuous L
  exact ENNReal.continuousOn_sub.comp_continuous
    (hF.prodMk hG)
    (fun t h => innerInt_h_ne_top L t (Prod.mk.inj h).2)

/-! ## Step 13: Everywhere inner integral equality -/

private theorem crossDiff_everywhere_zero
    (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) :
    ∀ t ∈ Ioo 0 (2 * Real.log cutoffLambda),
    innerInt (f_tilde ideal.B (Real.log cutoffLambda)) t +
    innerInt (g_tilde ideal.B (Real.log cutoffLambda)) t =
    innerInt (h_tilde (Real.log cutoffLambda)) t := by
  set L := Real.log cutoffLambda
  have h_ae_zero :
      ∀ᵐ t ∂(volume.restrict (Ioo 0 (2 * L))),
      (innerInt (f_tilde ideal.B L) t +
       innerInt (g_tilde ideal.B L) t) -
       innerInt (h_tilde L) t = 0 := by
    filter_upwards [inner_integral_indicator_ae_eq
        cutoffLambda hLam ideal]
      with t ht
    rw [ht]; exact tsub_self _
  have h_all := continuous_ae_zero_imp_zero
    (crossDiff_continuous ideal.B_measurable (L := L))
    h_ae_zero
  intro t ht
  have h_sub := h_all t ht
  -- h_sub : (f+g) - h = 0, need f+g = h
  have h_le := inner_integral_indicator_ge
    ideal.B_subset ideal.B_measurable t
  exact le_antisymm
    (tsub_eq_zero_iff_le.mp h_sub) h_le

/-! ## Step 14: Pointwise norm equality a.e. for each t -/

private theorem nnnorm_sq_ae_eq
    (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda)
    (t : ℝ) (ht : t ∈ Ioo 0 (2 * Real.log cutoffLambda)) :
    (fun u => (‖h_tilde (Real.log cutoffLambda) u -
      translationOp t (h_tilde (Real.log cutoffLambda)) u‖₊ :
        ENNReal) ^ (2 : ℝ)) =ᵐ[volume]
    (fun u => (‖f_tilde ideal.B (Real.log cutoffLambda) u -
      translationOp t (f_tilde ideal.B
        (Real.log cutoffLambda)) u‖₊ :
        ENNReal) ^ (2 : ℝ) +
      (‖g_tilde ideal.B (Real.log cutoffLambda) u -
      translationOp t (g_tilde ideal.B
        (Real.log cutoffLambda)) u‖₊ :
        ENNReal) ^ (2 : ℝ)) := by
  set L := Real.log cutoffLambda
  have h_eq := crossDiff_everywhere_zero cutoffLambda hLam ideal t ht
  -- h_eq : innerInt(f) + innerInt(g) = innerInt(h)
  -- Pointwise: h ≤ f + g
  -- Integral: ∫(f+g) = ∫h
  -- → h = f+g a.e.
  have h_le : ∀ u,
      (‖h_tilde L u - translationOp t (h_tilde L) u‖₊ :
        ENNReal) ^ (2 : ℝ) ≤
      (‖f_tilde ideal.B L u - translationOp t
        (f_tilde ideal.B L) u‖₊ : ENNReal) ^ (2 : ℝ) +
      (‖g_tilde ideal.B L u - translationOp t
        (g_tilde ideal.B L) u‖₊ : ENNReal) ^ (2 : ℝ) :=
    nnnorm_sq_indicator_ge ideal.B_subset t
  have h_meas : Measurable (fun u =>
      (‖f_tilde ideal.B L u - translationOp t
        (f_tilde ideal.B L) u‖₊ : ENNReal) ^ (2 : ℝ) +
      (‖g_tilde ideal.B L u - translationOp t
        (g_tilde ideal.B L) u‖₊ : ENNReal) ^ (2 : ℝ)) :=
    (measurable_inner_integrand
      (measurable_f_tilde ideal.B_measurable L) t).add
    (measurable_inner_integrand
      (measurable_g_tilde ideal.B_measurable L) t)
  have h_int_eq : ∫⁻ u, ((‖f_tilde ideal.B L u -
        translationOp t (f_tilde ideal.B L) u‖₊ :
          ENNReal) ^ (2 : ℝ) +
      (‖g_tilde ideal.B L u - translationOp t
        (g_tilde ideal.B L) u‖₊ :
          ENNReal) ^ (2 : ℝ)) ∂volume =
      ∫⁻ u, (‖h_tilde L u - translationOp t
        (h_tilde L) u‖₊ : ENNReal) ^ (2 : ℝ) ∂volume := by
    rw [lintegral_add_left
      (measurable_inner_integrand
        (measurable_f_tilde ideal.B_measurable L) t)]
    exact h_eq
  exact ae_eq_of_ae_le_of_lintegral_le
    (Filter.Eventually.of_forall h_le)
    (innerInt_h_ne_top L t)
    h_meas.aemeasurable
    h_int_eq.le

/-! ## Step 15: Cross indicator vanishes where norms agree -/

/-- If crossIndicator B L t u ≠ 0 then ‖f diff‖² + ‖g diff‖² > ‖h diff‖² -/
private theorem crossIndicator_contradicts_eq
    {B : Set ℝ} (_hB : B ⊆ logInterval L) (t : ℝ) (u : ℝ)
    (h_cross : crossIndicator B L t u ≠ 0)
    (h_eq : (‖h_tilde L u - translationOp t
      (h_tilde L) u‖₊ : ENNReal) ^ (2 : ℝ) =
      (‖f_tilde B L u - translationOp t
        (f_tilde B L) u‖₊ : ENNReal) ^ (2 : ℝ) +
      (‖g_tilde B L u - translationOp t
        (g_tilde B L) u‖₊ : ENNReal) ^ (2 : ℝ)) :
    False := by
  -- crossIndicator ≠ 0 means u ∈ I∩B and u-t ∈ I\B
  unfold crossIndicator at h_cross
  simp only [mul_ne_zero_iff] at h_cross
  obtain ⟨h1, h2⟩ := h_cross
  have h1_mem : u ∈ logInterval L ∩ B := by
    by_contra h_nmem; exact h1 (indicator_of_notMem h_nmem (1 : ℝ → ENNReal))
  have h2_mem : u ∈ (· - t) ⁻¹' (logInterval L \ B) := by
    by_contra h_nmem; exact h2 (indicator_of_notMem h_nmem (1 : ℝ → ENNReal))
  obtain ⟨hI_u, hB_u⟩ := h1_mem
  have hI_ut : u - t ∈ logInterval L := h2_mem.1
  have hB_ut : u - t ∉ B := h2_mem.2
  -- Evaluate: f(u)=1, f(u-t)=0, g(u)=0, g(u-t)=1, h(u)=1, h(u-t)=1
  have hnut_diff : u - t ∈ logInterval L \ B := ⟨hI_ut, hB_ut⟩
  simp only [f_tilde, g_tilde, h_tilde, translationOp_apply, zeroExtend,
    indicator_of_mem hI_u, indicator_of_mem hI_ut,
    indicator_of_mem hB_u, indicator_of_notMem hB_ut,
    indicator_of_notMem (show u ∉ logInterval L \ B from fun h => h.2 hB_u),
    indicator_of_mem hnut_diff,
    sub_self, sub_zero, zero_sub,
    nnnorm_zero, nnnorm_one, nnnorm_neg,
    ENNReal.coe_zero, ENNReal.coe_one,
    zero_rpow_of_pos (by norm_num : (0:ℝ) < 2),
    ENNReal.one_rpow] at h_eq
  norm_num at h_eq

/-- If crossIndicator (I\B) L t u ≠ 0, same contradiction -/
private theorem crossIndicator_compl_contradicts_eq
    {B : Set ℝ} (_hB : B ⊆ logInterval L) (t : ℝ) (u : ℝ)
    (h_cross : crossIndicator (logInterval L \ B) L t u ≠ 0)
    (h_eq : (‖h_tilde L u - translationOp t
      (h_tilde L) u‖₊ : ENNReal) ^ (2 : ℝ) =
      (‖f_tilde B L u - translationOp t
        (f_tilde B L) u‖₊ : ENNReal) ^ (2 : ℝ) +
      (‖g_tilde B L u - translationOp t
        (g_tilde B L) u‖₊ : ENNReal) ^ (2 : ℝ)) :
    False := by
  -- crossIndicator(I\B) ≠ 0 means u ∈ I∩(I\B) and u-t ∈ I\(I\B)
  unfold crossIndicator at h_cross
  simp only [mul_ne_zero_iff] at h_cross
  obtain ⟨h1, h2⟩ := h_cross
  have h1_mem : u ∈ logInterval L ∩ (logInterval L \ B) := by
    by_contra h_nmem; exact h1 (indicator_of_notMem h_nmem (1 : ℝ → ENNReal))
  have h2_mem : u ∈ (· - t) ⁻¹' (logInterval L \ (logInterval L \ B)) := by
    by_contra h_nmem; exact h2 (indicator_of_notMem h_nmem (1 : ℝ → ENNReal))
  obtain ⟨hI_u, _, hB_u⟩ := h1_mem
  have hI_ut : u - t ∈ logInterval L := h2_mem.1
  have hB_ut : u - t ∈ B := by
    by_contra hB_ut
    exact h2_mem.2 ⟨hI_ut, hB_ut⟩
  -- Evaluate: f(u)=0, f(u-t)=1, g(u)=1, g(u-t)=0, h(u)=1, h(u-t)=1
  have hu_diff : u ∈ logInterval L \ B := ⟨hI_u, hB_u⟩
  have hnut_ndiff : u - t ∉ logInterval L \ B := fun h => h.2 hB_ut
  simp only [f_tilde, g_tilde, h_tilde, translationOp_apply, zeroExtend,
    indicator_of_mem hI_u, indicator_of_mem hI_ut,
    indicator_of_notMem hB_u, indicator_of_mem hB_ut,
    indicator_of_mem hu_diff, indicator_of_notMem hnut_ndiff,
    sub_self, sub_zero, zero_sub,
    nnnorm_zero, nnnorm_one, nnnorm_neg,
    ENNReal.coe_zero, ENNReal.coe_one,
    zero_rpow_of_pos (by norm_num : (0:ℝ) < 2),
    ENNReal.one_rpow] at h_eq
  norm_num at h_eq

/-! ## Step 16: Cross indicators vanish a.e. for each t -/

private theorem cross_ae_zero
    (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda)
    (t : ℝ) (ht : t ∈ Ioo 0 (2 * Real.log cutoffLambda)) :
    ∀ᵐ u ∂volume,
    crossIndicator ideal.B (Real.log cutoffLambda) t u = 0 ∧
    crossIndicator
      (logInterval (Real.log cutoffLambda) \ ideal.B)
      (Real.log cutoffLambda) t u = 0 := by
  set L := Real.log cutoffLambda
  have h_ae := nnnorm_sq_ae_eq cutoffLambda hLam ideal t ht
  filter_upwards [h_ae] with u hu
  constructor
  · by_contra h_ne
    exact crossIndicator_contradicts_eq ideal.B_subset t u
      h_ne hu
  · by_contra h_ne
    exact crossIndicator_compl_contradicts_eq
      ideal.B_subset t u h_ne hu

/-! ## Main theorem -/

/-- **Proposition 10, Steps 4–9**: The indicator function
    1_B is translation-invariant a.e. on I ∩ (I+t) for all
    t ∈ (0, 2L).

    Reference: lamportform.tex, Proposition 10, Steps 4–9. -/
theorem indicator_invariant_of_ideal
    (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) :
    ∀ t, 0 < t → t < 2 * Real.log cutoffLambda →
    ∀ᵐ u ∂(volume.restrict
      (logInterval (Real.log cutoffLambda) ∩
        Set.preimage (· - t)
          (logInterval (Real.log cutoffLambda)))),
    ideal.B.indicator (1 : ℝ → ℝ) u =
    ideal.B.indicator (1 : ℝ → ℝ) (u - t) := by
  set L := Real.log cutoffLambda
  set I := logInterval L
  intro t ht_pos ht_bound
  have ht : t ∈ Ioo 0 (2 * L) := ⟨ht_pos, ht_bound⟩
  have h_ae := cross_ae_zero cutoffLambda hLam ideal t ht
  rw [ae_restrict_iff'
    ((measurableSet_logInterval L).inter
      ((measurableSet_logInterval L).preimage
        (measurable_sub_const t)))]
  filter_upwards [h_ae] with u hu hu_mem
  obtain ⟨hu_I, hu_It⟩ := hu_mem
  obtain ⟨h_cross_B, h_cross_Bc⟩ := hu
  by_cases hB_u : u ∈ ideal.B
  · by_cases hB_ut : (u - t) ∈ ideal.B
    · simp [indicator_of_mem hB_u, indicator_of_mem hB_ut]
    · exfalso
      -- crossIndicator B = 0 but u ∈ B∩I and u-t ∈ I\B → cross ≠ 0
      have : crossIndicator ideal.B L t u ≠ 0 := by
        unfold crossIndicator
        rw [indicator_of_mem
            (show u ∈ I ∩ ideal.B from ⟨hu_I, hB_u⟩),
          indicator_of_mem
            (show u ∈ (· - t) ⁻¹' (I \ ideal.B)
              from ⟨hu_It, hB_ut⟩)]
        simp
      exact this h_cross_B
  · by_cases hB_ut : (u - t) ∈ ideal.B
    · exfalso
      -- crossIndicator (I\B) = 0 but u ∈ (I\B) and u-t ∈ B → cross ≠ 0
      have : crossIndicator (I \ ideal.B) L t u ≠ 0 := by
        unfold crossIndicator
        rw [indicator_of_mem
            (show u ∈ I ∩ (I \ ideal.B)
              from ⟨hu_I, hu_I, hB_u⟩),
          indicator_of_mem
            (show u ∈ (· - t) ⁻¹' (I \ (I \ ideal.B))
              from ⟨hu_It, fun h => h.2 hB_ut⟩)]
        simp
      exact this h_cross_Bc
    · simp [indicator_of_notMem hB_u,
        indicator_of_notMem hB_ut]

end

end ConnesLean
