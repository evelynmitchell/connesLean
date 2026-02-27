/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Indicator Energy Criterion — Lemma 7

Reference: lamportform.tex, Lemma 7 (lines 647–696).

If the energy form vanishes on an indicator function `1_B` for measurable `B ⊆ I`,
then `B` must be either null or conull in `I`. The proof extracts the archimedean
and prime energy components, uses strong continuity of translations to upgrade
ae vanishing to pointwise vanishing, and then applies the null-or-conull theorem
from Stage 4.
-/

import ConnesLean.Stage4.NullOrConull
import ConnesLean.Stage2.EnergyForm

namespace ConnesLean

open MeasureTheory Set Real Filter Metric

noncomputable section

/-! ## Energy form component extraction -/

/-- If the energy form vanishes, the archimedean energy integral is zero. -/
theorem archEnergy_eq_zero_of_energyForm_eq_zero
    {cutoffLambda : ℝ} {G : ℝ → ℂ} (h : energyForm cutoffLambda G = 0) :
    archEnergyIntegral G (Real.log cutoffLambda) = 0 :=
  (add_eq_zero.mp h).1

/-- If the energy form vanishes, each prime energy term is zero. -/
theorem primeEnergy_eq_zero_of_energyForm_eq_zero
    {cutoffLambda : ℝ} {G : ℝ → ℂ} (h : energyForm cutoffLambda G = 0) :
    ∀ p ∈ primeFinset cutoffLambda,
      totalPrimeEnergy p cutoffLambda G (Real.log cutoffLambda) = 0 :=
  Finset.sum_eq_zero_iff.mp (add_eq_zero.mp h).2

/-- If the weighted energy integrand vanishes at a positive time,
    the norm-squared integral is zero. -/
theorem translationOp_normSq_zero_of_weighted_zero
    {G : ℝ → ℂ} {L t : ℝ} (ht : 0 < t)
    (h : archEnergyIntegrand G L t = 0) :
    ∫⁻ u, ‖zeroExtend G (logInterval L) u -
      translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ)
      ∂volume = 0 := by
  unfold archEnergyIntegrand at h
  rcases mul_eq_zero.mp h with h_wt | h_int
  · exfalso
    have h_pos : 0 < (archWeight t).toNNReal := by
      rw [Real.toNNReal_pos]
      exact archWeight_pos ht
    exact absurd (ENNReal.coe_eq_zero.mp h_wt) (ne_of_gt h_pos)
  · exact h_int

/-- The map `t ↦ (archWeight t).toNNReal` is measurable. -/
theorem measurable_archWeight_toNNReal :
    Measurable (fun t : ℝ => (archWeight t).toNNReal) := by
  unfold archWeight
  exact measurable_real_toNNReal.comp
    ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh))

/-! ## Continuity and ae-zero upgrade -/

/-- A continuous `ENNReal`-valued function that is ae-zero on an open interval
    is pointwise zero on that interval. -/
theorem continuous_ae_zero_imp_zero
    {f : ℝ → ENNReal} {a b : ℝ} (hf : Continuous f)
    (h_ae : ∀ᵐ t ∂(volume.restrict (Ioo a b)), f t = 0) :
    ∀ t ∈ Ioo a b, f t = 0 := by
  intro t₀ ht₀
  by_contra h_ne
  have h_pos : 0 < f t₀ := pos_iff_ne_zero.mpr h_ne
  -- f⁻¹(Ioi 0) ∩ Ioo a b is open and contains t₀
  have h_open : IsOpen (Ioo a b ∩ f ⁻¹' Ioi 0) :=
    isOpen_Ioo.inter (hf.isOpen_preimage _ isOpen_Ioi)
  have h_mem : t₀ ∈ Ioo a b ∩ f ⁻¹' Ioi 0 :=
    ⟨ht₀, mem_preimage.mpr (mem_Ioi.mpr h_pos)⟩
  -- Find δ-ball inside the open set
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.isOpen_iff.mp h_open t₀ h_mem
  set δ' := δ / 2 with hδ'_def
  have hδ'_pos : 0 < δ' := by linarith
  -- Subinterval Ioo(t₀ - δ', t₀ + δ') ⊆ ball t₀ δ
  have h_sub_ball : Ioo (t₀ - δ') (t₀ + δ') ⊆ Metric.ball t₀ δ := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- Subinterval ⊆ Ioo a b (from ball containment)
  have h_sub_Ioo : Ioo (t₀ - δ') (t₀ + δ') ⊆ Ioo a b :=
    fun x hx => (hδ_ball (h_sub_ball hx)).1
  -- Every point in subinterval has f > 0
  have h_f_pos : ∀ x ∈ Ioo (t₀ - δ') (t₀ + δ'), 0 < f x :=
    fun x hx => (hδ_ball (h_sub_ball hx)).2
  -- But f = 0 ae on the subinterval
  have h_ae_sub : ∀ᵐ x ∂(volume.restrict (Ioo (t₀ - δ') (t₀ + δ'))), f x = 0 :=
    ae_restrict_of_ae_restrict_of_subset h_sub_Ioo h_ae
  -- The subinterval has positive measure
  have h_vol_pos : 0 < volume (Ioo (t₀ - δ') (t₀ + δ')) := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
  have h_ne_zero : volume.restrict (Ioo (t₀ - δ') (t₀ + δ')) ≠ 0 := by
    intro h_eq; apply ne_of_gt h_vol_pos
    have : volume.restrict (Ioo (t₀ - δ') (t₀ + δ'))
      (Ioo (t₀ - δ') (t₀ + δ')) = 0 := by simp [h_eq]
    rwa [Measure.restrict_apply_self] at this
  -- Extract a witness: ∃ x, f x = 0 ∧ x ∈ subinterval
  haveI : NeBot (ae (volume.restrict (Ioo (t₀ - δ') (t₀ + δ')))) :=
    ae_neBot.mpr h_ne_zero
  obtain ⟨x, hx_zero, hx_mem⟩ :=
    (h_ae_sub.and (ae_restrict_mem measurableSet_Ioo)).exists
  exact absurd hx_zero (ne_of_gt (h_f_pos x hx_mem))

/-! ## L² norm zero implies ae equality -/

/-- If the L² distance (as `∫⁻ ‖f - g‖₊ ^ 2`) is zero, then `f = g` a.e. -/
theorem ae_eq_of_lintegral_nnnorm_rpow_zero
    {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (h : ∫⁻ u, ‖f u - g u‖₊ ^ (2 : ℝ) ∂volume = 0) :
    ∀ᵐ u ∂volume, f u = g u := by
  have h_meas : Measurable (fun u => (‖f u - g u‖₊ : ENNReal) ^ (2 : ℝ)) :=
    ((hf.sub hg).nnnorm.coe_nnreal_ennreal.pow_const 2)
  have h_ae := (lintegral_eq_zero_iff h_meas).mp h
  filter_upwards [h_ae] with u hu
  simp only [Pi.zero_apply] at hu
  -- hu : ↑‖f u - g u‖₊ ^ (2:ℝ) = 0
  have h1 : (‖f u - g u‖₊ : ENNReal) = 0 := by
    rcases ENNReal.rpow_eq_zero_iff.mp hu with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · norm_num at h
  rw [ENNReal.coe_eq_zero, nnnorm_eq_zero, sub_eq_zero] at h1
  exact h1

/-! ## Indicator equality conversion (ℂ → ℝ) -/

/-- Convert ae equality of ℂ-valued zero-extended indicators to
    ae equality of ℝ-valued indicators on the overlap region. -/
theorem indicator_ae_eq_on_overlap
    {B : Set ℝ} {L t : ℝ}
    (h_ae : ∀ᵐ u ∂volume,
      zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) u =
      zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) (u - t)) :
    ∀ᵐ u ∂(volume.restrict (logInterval L ∩ preimage (· - t) (logInterval L))),
      B.indicator (1 : ℝ → ℝ) u = B.indicator (1 : ℝ → ℝ) (u - t) := by
  have h_ae' : ∀ᵐ u ∂(volume.restrict (logInterval L ∩ preimage (· - t) (logInterval L))),
      zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) u =
      zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) (u - t) :=
    ae_restrict_of_ae h_ae
  have h_measI := measurableSet_logInterval L
  have h_mem : ∀ᵐ u ∂(volume.restrict (logInterval L ∩ preimage (· - t) (logInterval L))),
      u ∈ logInterval L ∩ preimage (· - t) (logInterval L) :=
    ae_restrict_mem (h_measI.inter (h_measI.preimage (measurable_id.sub measurable_const)))
  filter_upwards [h_ae', h_mem] with u hu hu_mem
  have hu_I := hu_mem.1
  have hu_t_I : u - t ∈ logInterval L := hu_mem.2
  rw [zeroExtend_apply_mem hu_I, zeroExtend_apply_mem hu_t_I] at hu
  -- hu : B.indicator (1 : ℝ → ℂ) u = B.indicator (1 : ℝ → ℂ) (u - t)
  by_cases hB : u ∈ B <;> by_cases hBt : (u - t) ∈ B
  · simp [indicator_of_mem hB, indicator_of_mem hBt]
  · exfalso; simp [indicator_of_mem hB, indicator_of_notMem hBt] at hu
  · exfalso; simp [indicator_of_notMem hB, indicator_of_mem hBt] at hu
  · simp [indicator_of_notMem hB, indicator_of_notMem hBt]

/-! ## Main theorem -/

/-- **Lemma 7 (Indicator Energy Criterion)**: If `E_λ(1_B) = 0` for
    measurable `B ⊆ I`, then `volume B = 0` or `volume (I \ B) = 0`.

    Reference: lamportform.tex, Lemma 7 (lines 647–696). -/
theorem energyForm_indicator_null_or_conull
    {cutoffLambda : ℝ} {B : Set ℝ} (hLam : 1 < cutoffLambda)
    (hB_meas : MeasurableSet B) (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (h_energy : energyForm cutoffLambda (B.indicator (1 : ℝ → ℂ)) = 0) :
    volume B = 0 ∨ volume (logInterval (Real.log cutoffLambda) \ B) = 0 := by
  set L := Real.log cutoffLambda with hL_def
  set I := logInterval L with hI_def
  set G := B.indicator (1 : ℝ → ℂ) with hG_def
  set φ := zeroExtend G I with hφ_def
  have hL_pos : 0 < L := Real.log_pos hLam
  -- Step 1: Extract arch = 0
  have h_arch := archEnergy_eq_zero_of_energyForm_eq_zero h_energy
  -- Step 2: archEnergyIntegrand = 0 a.e. on (0, 2L)
  have hG_meas : Measurable G := measurable_const.indicator hB_meas
  have h_meas_integrand : Measurable (archEnergyIntegrand G L) := by
    unfold archEnergyIntegrand
    exact measurable_archWeight_toNNReal.coe_nnreal_ennreal.mul
      (measurable_archEnergyIntegrand hG_meas L)
  have h_integrand_ae : ∀ᵐ t ∂(volume.restrict (Ioo 0 (2 * L))),
      archEnergyIntegrand G L t = 0 := by
    have h_unfold : archEnergyIntegral G L =
        ∫⁻ t in Ioo 0 (2 * L), archEnergyIntegrand G L t ∂volume := rfl
    rw [h_unfold] at h_arch
    exact (lintegral_eq_zero_iff h_meas_integrand).mp h_arch
  -- Step 3: ‖φ - S_t φ‖² = 0 for a.e. t ∈ (0, 2L)
  have h_normSq_ae : ∀ᵐ t ∂(volume.restrict (Ioo 0 (2 * L))),
      ∫⁻ u, ‖φ u - translationOp t φ u‖₊ ^ (2 : ℝ) ∂volume = 0 := by
    filter_upwards [h_integrand_ae, ae_restrict_mem measurableSet_Ioo] with t ht ht_mem
    exact translationOp_normSq_zero_of_weighted_zero ht_mem.1 ht
  -- Step 4: Continuity upgrade — pointwise zero on (0, 2L)
  have hφ_meas : Measurable φ := by
    rw [hφ_def, zeroExtend_eq_indicator]
    exact hG_meas.indicator (measurableSet_logInterval L)
  have hφ_sq : ∫⁻ u, ‖φ u‖₊ ^ (2 : ℝ) ∂volume < ⊤ := by
    have h_zero_rpow : (0 : ENNReal) ^ (2 : ℝ) = 0 :=
      ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)
    have h_one_rpow : (1 : ENNReal) ^ (2 : ℝ) = 1 := ENNReal.one_rpow _
    have h_le : ∀ u, (‖φ u‖₊ : ENNReal) ^ (2 : ℝ) ≤
        I.indicator (fun _ => (1 : ENNReal)) u := by
      intro u
      simp only [hφ_def, zeroExtend_eq_indicator]
      by_cases hu : u ∈ I
      · simp only [indicator_of_mem hu]
        rw [hG_def]
        by_cases hB : u ∈ B
        · simp only [indicator_of_mem hB, Pi.one_apply, nnnorm_one, ENNReal.coe_one, h_one_rpow]
          exact le_refl _
        · simp only [indicator_of_notMem hB, nnnorm_zero, ENNReal.coe_zero, h_zero_rpow]
          exact zero_le _
      · simp only [indicator_of_notMem hu, nnnorm_zero, ENNReal.coe_zero, h_zero_rpow]
        exact le_refl _
    calc ∫⁻ u, ‖φ u‖₊ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ u, I.indicator (fun _ => (1 : ENNReal)) u ∂volume := lintegral_mono h_le
      _ = volume I := lintegral_indicator_one (measurableSet_logInterval L)
      _ < ⊤ := by rw [hI_def, logInterval]; exact measure_Ioo_lt_top
  have h_cont := translation_norm_sq_continuous φ hφ_meas hφ_sq
  have h_normSq_zero : ∀ t ∈ Ioo 0 (2 * L),
      ∫⁻ u, ‖φ u - translationOp t φ u‖₊ ^ (2 : ℝ) ∂volume = 0 :=
    continuous_ae_zero_imp_zero h_cont h_normSq_ae
  -- Step 5: φ =ᵃᵉ S_t φ for each t ∈ (0, 2L)
  have h_ae_eq : ∀ t ∈ Ioo 0 (2 * L),
      ∀ᵐ u ∂volume, φ u = φ (u - t) := by
    intro t ht
    have := h_normSq_zero t ht
    exact ae_eq_of_lintegral_nnnorm_rpow_zero hφ_meas
      (hφ_meas.comp (measurable_id.sub measurable_const)) this
  -- Step 6: Convert to ℝ indicator ae equality on overlap
  have h_indicator_ae : ∀ t, 0 < t → t < 2 * L →
      ∀ᵐ u ∂(volume.restrict (I ∩ preimage (· - t) I)),
        B.indicator (1 : ℝ → ℝ) u = B.indicator (1 : ℝ → ℝ) (u - t) := by
    intro t ht_pos ht_bound
    exact indicator_ae_eq_on_overlap (h_ae_eq t ⟨ht_pos, ht_bound⟩)
  -- Step 7: Construct IndicatorTranslationInvariant and apply null_or_conull
  have h_inv : IndicatorTranslationInvariant B I (2 * L) :=
    { ε_pos := by linarith
      B_measurable := hB_meas
      B_subset := hB_sub
      I_open := ⟨-L, L, by linarith, rfl⟩
      ae_shift := h_indicator_ae }
  exact null_or_conull_of_translation_invariant h_inv

end

end ConnesLean
