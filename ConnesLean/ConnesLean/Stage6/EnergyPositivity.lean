/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Energy Positivity — Remark 4

Reference: lamportform.tex, Remark 4 (lines 698–723).

If the energy form vanishes on an indicator `1_B` for measurable `B ⊆ I`,
then `B` must be **null** (not merely null or conull as in Lemma 7).
The key new ingredient is `E_λ(1) > 0`, which rules out the conull case.
-/

import ConnesLean.Stage6.IndicatorEnergy

/-!
# Energy Positivity — Remark 4

Sharpens the indicator energy criterion (Lemma 7) to rule out the conull case
by proving `E_λ(1) > 0`. The archimedean energy integral of the constant function
is positive because translation by any `t ∈ (0, 2L)` moves the support boundary,
creating a region where `1_I` and `S_t(1_I)` disagree.

Reference: lamportform.tex, Remark 4 (lines 698–723).
-/

namespace ConnesLean

open MeasureTheory Set Real Filter

noncomputable section

/-! ## Inner integral positivity -/

/-- For `0 < t < 2L` with `L > 0`, the L² norm of
    `zeroExtend 1 I - S_t(zeroExtend 1 I)` is positive.
    The functions disagree on `Ioo (-L) (-L + t)`. -/
theorem lintegral_indicator_diff_pos
    {L t : ℝ} (_hL : 0 < L) (ht : 0 < t) (htL : t < 2 * L) :
    0 < ∫⁻ u, ‖zeroExtend (1 : ℝ → ℂ) (logInterval L) u -
      translationOp t (zeroExtend (1 : ℝ → ℂ) (logInterval L)) u‖₊
        ^ (2 : ℝ) ∂volume := by
  set I := logInterval L
  set φ := zeroExtend (1 : ℝ → ℂ) I
  have hφ_meas : Measurable φ :=
    measurable_const.indicator (measurableSet_logInterval L)
  have h_meas : Measurable
      (fun u => (‖φ u - translationOp t φ u‖₊ : ENNReal) ^ (2 : ℝ)) :=
    Measurable.pow_const (Measurable.coe_nnreal_ennreal
      (Measurable.nnnorm (hφ_meas.sub
        (hφ_meas.comp (measurable_id.sub measurable_const))))) _
  rw [lintegral_pos_iff_support h_meas]
  -- Ioo (-L) (-L + t) ⊆ support: there φ u = 1 but φ(u-t) = 0
  have h_sub : Ioo (-L) (-L + t) ⊆ Function.support
      (fun u => (‖φ u - translationOp t φ u‖₊ : ENNReal) ^ (2 : ℝ)) := by
    intro u hu
    simp only [Function.mem_support]
    obtain ⟨hu_lo, hu_hi⟩ := mem_Ioo.mp hu
    have hu_mem : u ∈ I := mem_Ioo.mpr ⟨hu_lo, by linarith⟩
    have hu_nmem : u - t ∉ I := by
      simp only [I, logInterval, mem_Ioo, not_and_or, not_lt]
      left; linarith
    have h1 : φ u = 1 := by simp [φ, zeroExtend_apply_mem hu_mem]
    have h2 : φ (u - t) = 0 := by
      simp [φ, zeroExtend_apply_nmem hu_nmem]
    rw [translationOp_apply]; simp [h1, h2]
  exact lt_of_lt_of_le
    (by rw [Real.volume_Ioo]
        exact ENNReal.ofReal_pos.mpr (by linarith))
    (measure_mono h_sub)

/-! ## Archimedean energy positivity -/

/-- The archimedean energy integral of the constant function `1` is positive
    when `cutoffLambda > 1`. Each point `t ∈ (0, 2L)` contributes a positive
    integrand since `archWeight(t) > 0` and the inner integral is positive. -/
theorem archEnergyIntegral_one_pos
    {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    0 < archEnergyIntegral (1 : ℝ → ℂ) (Real.log cutoffLambda) := by
  set L := Real.log cutoffLambda
  have hL : 0 < L := Real.log_pos hLam
  unfold archEnergyIntegral
  have h_meas : Measurable (archEnergyIntegrand (1 : ℝ → ℂ) L) := by
    unfold archEnergyIntegrand
    exact measurable_archWeight_toNNReal.coe_nnreal_ennreal.mul
      (measurable_archEnergyIntegrand measurable_const L)
  rw [lintegral_pos_iff_support h_meas]
  -- Ioo 0 (2L) ⊆ support because integrand is positive there
  suffices h_sub : Ioo 0 (2 * L) ⊆
      Function.support (archEnergyIntegrand (1 : ℝ → ℂ) L) by
    calc 0 < volume (Ioo 0 (2 * L)) := by
            rw [Real.volume_Ioo]
            exact ENNReal.ofReal_pos.mpr (by linarith)
      _ = volume (Ioo 0 (2 * L) ∩ Ioo 0 (2 * L)) := by
            rw [inter_self]
      _ ≤ volume (Function.support (archEnergyIntegrand 1 L) ∩
            Ioo 0 (2 * L)) :=
            measure_mono (inter_subset_inter_left _ h_sub)
      _ ≤ (volume.restrict (Ioo 0 (2 * L)))
            (Function.support (archEnergyIntegrand 1 L)) :=
            Measure.le_restrict_apply _ _
  intro t ht
  simp only [Function.mem_support]
  unfold archEnergyIntegrand
  exact ne_of_gt (ENNReal.mul_pos
    (ENNReal.coe_ne_zero.mpr
      (ne_of_gt (Real.toNNReal_pos.mpr (archWeight_pos ht.1))))
    (ne_of_gt (lintegral_indicator_diff_pos hL ht.1 ht.2)))

/-! ## Energy form positivity -/

/-- The energy form of the constant function `1` is positive:
    `E_λ(1) > 0`. This is the key fact that rules out the conull case
    in the indicator energy criterion. -/
theorem energyForm_one_pos
    {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    0 < energyForm cutoffLambda (1 : ℝ → ℂ) := by
  unfold energyForm
  exact lt_of_lt_of_le (archEnergyIntegral_one_pos hLam) le_self_add

/-! ## Conull indicator has the same energy as 1 -/

/-- Helper: if two functions are ae-equal after zero-extension, the
    archimedean energy integrand is pointwise equal. -/
private theorem archEnergyIntegrand_congr_ae {G₁ G₂ : ℝ → ℂ} {L : ℝ}
    (h_ae : zeroExtend G₁ (logInterval L) =ᵐ[volume]
            zeroExtend G₂ (logInterval L)) (t : ℝ) :
    archEnergyIntegrand G₁ L t = archEnergyIntegrand G₂ L t := by
  unfold archEnergyIntegrand; congr 1
  have h_shift : (fun u => zeroExtend G₁ (logInterval L) (u - t))
      =ᵐ[volume] (fun u => zeroExtend G₂ (logInterval L) (u - t)) :=
    h_ae.comp_tendsto
      (measurePreserving_sub_const t).quasiMeasurePreserving.tendsto_ae
  apply lintegral_congr_ae
  filter_upwards [h_ae, h_shift] with u hu1 hu2
  simp only [translationOp_apply, hu1, hu2]

/-- Helper: if two functions are ae-equal after zero-extension, each
    prime energy term is equal. -/
private theorem primeEnergyTerm_congr_ae {G₁ G₂ : ℝ → ℂ} {L : ℝ}
    (h_ae : zeroExtend G₁ (logInterval L) =ᵐ[volume]
            zeroExtend G₂ (logInterval L)) (p m : ℕ) :
    primeEnergyTerm p m G₁ L = primeEnergyTerm p m G₂ L := by
  unfold primeEnergyTerm; congr 1
  have h_shift :
      (fun u => zeroExtend G₁ (logInterval L) (u - ↑m * log ↑p))
      =ᵐ[volume]
      (fun u => zeroExtend G₂ (logInterval L) (u - ↑m * log ↑p)) :=
    h_ae.comp_tendsto
      (measurePreserving_sub_const _).quasiMeasurePreserving.tendsto_ae
  apply lintegral_congr_ae
  filter_upwards [h_ae, h_shift] with u hu1 hu2
  simp only [translationOp_apply, hu1, hu2]

/-- If `B` is conull in `I`, zero-extending `1_B` and `1` over `I` are ae-equal.
    The disagreement set is contained in `I \ B`, which has measure zero. -/
theorem zeroExtend_indicator_ae_eq_of_conull
    {B : Set ℝ} {L : ℝ}
    (_hB_sub : B ⊆ logInterval L)
    (hB_conull : volume (logInterval L \ B) = 0) :
    zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) =ᵐ[volume]
      zeroExtend (1 : ℝ → ℂ) (logInterval L) := by
  set I := logInterval L
  rw [Filter.EventuallyEq, ae_iff]
  apply le_antisymm _ (zero_le _)
  calc volume {a | ¬(zeroExtend (B.indicator (1 : ℝ → ℂ)) I a =
        zeroExtend (1 : ℝ → ℂ) I a)}
      ≤ volume (I \ B) := by
        apply measure_mono; intro u hu
        simp only [mem_setOf_eq] at hu
        by_cases hu_I : u ∈ I
        · exact ⟨hu_I, fun hu_B => hu (by
            simp [zeroExtend_apply_mem hu_I, indicator_of_mem hu_B])⟩
        · exact absurd (by simp [zeroExtend_apply_nmem hu_I]) hu
    _ = 0 := hB_conull

/-- If `B` is conull in `I`, then `E_λ(1_B) = E_λ(1)`.
    The ae-equality of the zero-extended functions propagates through
    the energy form via `lintegral_congr_ae`. -/
theorem energyForm_indicator_eq_one_of_conull
    {cutoffLambda : ℝ} {B : Set ℝ}
    (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (hB_conull : volume (logInterval (Real.log cutoffLambda) \ B) = 0) :
    energyForm cutoffLambda (B.indicator (1 : ℝ → ℂ)) =
      energyForm cutoffLambda (1 : ℝ → ℂ) := by
  set L := Real.log cutoffLambda
  have h_ae := zeroExtend_indicator_ae_eq_of_conull hB_sub hB_conull
  change archEnergyIntegral (B.indicator 1) L +
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda (B.indicator 1) L =
    archEnergyIntegral 1 L +
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda 1 L
  congr 1
  · -- arch equality
    change ∫⁻ t in Ioo 0 (2 * L),
        archEnergyIntegrand (B.indicator 1) L t =
      ∫⁻ t in Ioo 0 (2 * L), archEnergyIntegrand 1 L t
    congr 1; funext t
    exact archEnergyIntegrand_congr_ae h_ae t
  · -- prime equality
    apply Finset.sum_congr rfl; intro p _
    change ∑ m ∈ exponentFinset p cutoffLambda,
        primeEnergyTerm p m (B.indicator 1) L =
      ∑ m ∈ exponentFinset p cutoffLambda,
        primeEnergyTerm p m 1 L
    apply Finset.sum_congr rfl; intro m _
    exact primeEnergyTerm_congr_ae h_ae p m

/-! ## Main theorem -/

/-- **Remark 4 (Energy positivity)**: If `E_λ(1_B) = 0` for measurable `B ⊆ I`,
    then `volume B = 0`.

    Combines `energyForm_indicator_null_or_conull` (Lemma 7) with
    `energyForm_one_pos` to rule out the conull case: if `B` were conull,
    then `E_λ(1_B) = E_λ(1) > 0`, contradicting `E_λ(1_B) = 0`.

    Reference: lamportform.tex, Remark 4 (lines 698–723). -/
theorem energyForm_indicator_null
    {cutoffLambda : ℝ} {B : Set ℝ}
    (hLam : 1 < cutoffLambda)
    (hB_meas : MeasurableSet B)
    (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (h_energy : energyForm cutoffLambda
      (B.indicator (1 : ℝ → ℂ)) = 0) :
    volume B = 0 := by
  rcases energyForm_indicator_null_or_conull hLam hB_meas hB_sub
      h_energy with h | h
  · exact h
  · -- Conull case: E_λ(1_B) = E_λ(1) > 0, contradiction
    exfalso
    have h_eq := energyForm_indicator_eq_one_of_conull hB_sub h
    rw [h_energy] at h_eq
    exact absurd h_eq.symm (ne_of_gt (energyForm_one_pos hLam))

end

end ConnesLean
