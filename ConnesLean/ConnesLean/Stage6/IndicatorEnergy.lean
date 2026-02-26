/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Indicator-Energy Criterion — Lemma 7 + Remark 4

Reference: lamportform.tex, Section 6.1, lines 647–723.

**Lemma 7**: If E_λ(1_B) = 0, then m(B) = 0 or m(I \ B) = 0.

The proof follows five steps:
1. The archimedean contribution vanishes (nonneg terms sum to 0 → each = 0).
2. ‖1̃_B − S_t 1̃_B‖² = 0 for a.e. t (positive weight w(t) > 0).
3. Upgrade a.e. to all t via continuity of t ↦ ‖φ − S_t φ‖².
4. Deduce 1_B(u) = 1_B(u−t) for a.e. u ∈ I ∩ (I+t).
5. Apply Stage 4's `null_or_conull_of_translation_invariant`.

**Remark 4**: E_λ(1) > 0 (symmetric difference 2t), so E_λ(1_B) = 0 forces m(B) = 0.

## Axiom

One axiom is used for the strong continuity of translations in L² (Step 3):
the map `t ↦ ∫ ‖φ(u) − φ(u−t)‖² du` is continuous for any `φ : ℝ → ℂ`.
This is a standard result (Engel-Nagel, Thm I.5.8; or by dominated convergence)
but requires L² strong continuity infrastructure not currently available in
Mathlib. The axiom lives in `Stage2.TranslationOperator` for reusability.
-/

import ConnesLean.Stage4.NullOrConull
import ConnesLean.Stage2.EnergyForm

namespace ConnesLean

open MeasureTheory Real Finset Set

noncomputable section

/-! ## Step 1: Vanishing energy implies vanishing components -/

/-- If E_λ(G) = 0, then the archimedean energy integral vanishes.

    Reference: lamportform.tex, Lemma 7, Step 1. -/
theorem archEnergy_eq_zero_of_energyForm_eq_zero {cutoffLambda : ℝ} {G : ℝ → ℂ}
    (h : energyForm cutoffLambda G = 0) :
    archEnergyIntegral G (Real.log cutoffLambda) = 0 :=
  (add_eq_zero.mp (by unfold energyForm at h; exact h)).1

/-- If E_λ(G) = 0, then each prime energy term vanishes. -/
theorem primeEnergy_eq_zero_of_energyForm_eq_zero {cutoffLambda : ℝ} {G : ℝ → ℂ}
    (h : energyForm cutoffLambda G = 0) :
    ∀ p ∈ primeFinset cutoffLambda,
      totalPrimeEnergy p cutoffLambda G (Real.log cutoffLambda) = 0 := by
  have h2 := (add_eq_zero.mp (by unfold energyForm at h; exact h)).2
  exact fun p hp => Finset.sum_eq_zero_iff.mp h2 p hp

/-! ## Step 2: Weighted integrand vanishes → L² norm vanishes -/

/-- If w(t) · ‖G̃ − S_t G̃‖² = 0 and t > 0 (so w(t) > 0), then ‖G̃ − S_t G̃‖² = 0.

    Reference: lamportform.tex, Lemma 7, Step 2. -/
theorem translationOp_normSq_zero_of_weighted_zero {G : ℝ → ℂ} {L t : ℝ}
    (ht : 0 < t) (h : archEnergyIntegrand G L t = 0) :
    ∫⁻ u, ‖zeroExtend G (logInterval L) u -
           translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ) ∂volume = 0 := by
  unfold archEnergyIntegrand at h
  have hw_nnreal : (archWeight t).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero]; push_neg
    exact archWeight_pos ht
  exact (mul_eq_zero.mp h).resolve_left (ENNReal.coe_ne_zero.mpr hw_nnreal)

/-! ## Step 3: Continuity upgrade from a.e. to everywhere

The axiom `translation_norm_sq_continuous` (strong continuity of translations
in L²) lives in `Stage2.TranslationOperator` for reusability. -/

/-- A continuous ENNReal-valued function that vanishes a.e. on an open interval
    vanishes everywhere on that interval.

    Proof: if f(t₀) > 0, then by continuity f > 0 on an open neighborhood,
    which has positive measure — contradicting f = 0 a.e. -/
theorem continuous_ae_zero_imp_zero {f : ℝ → ENNReal} {a b : ℝ}
    (hf : Continuous f)
    (h_ae : ∀ᵐ t ∂(volume.restrict (Ioo a b)), f t = 0) :
    ∀ t ∈ Ioo a b, f t = 0 := by
  intro t ht
  by_contra h_ne
  have h_pos : 0 < f t := pos_iff_ne_zero.mpr h_ne
  have h_open_pre : IsOpen (f ⁻¹' (Ioi 0)) := hf.isOpen_preimage _ isOpen_Ioi
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp h_open_pre t
    (mem_preimage.mpr (mem_Ioi.mpr h_pos))
  -- Take δ' small enough to stay inside (a, b) and ball(t, δ)
  have hta : 0 < t - a := by linarith [ht.1]
  have hbt : 0 < b - t := by linarith [ht.2]
  have hm_pos : 0 < min δ (min (t - a) (b - t)) := lt_min hδ_pos (lt_min hta hbt)
  set δ' := min δ (min (t - a) (b - t)) / 2
  have hδ'_pos : 0 < δ' := by positivity
  have hδ'_le_δ : δ' < δ := by
    calc δ' ≤ δ / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      _ < δ := by linarith
  have hδ'_le_ta : δ' ≤ (t - a) / 2 := by
    exact div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num)
  have hδ'_le_bt : δ' ≤ (b - t) / 2 := by
    exact div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (min_le_right _ _)) (by norm_num)
  have h_sub_ab : Ioo (t - δ') (t + δ') ⊆ Ioo a b :=
    Ioo_subset_Ioo (by nlinarith) (by nlinarith)
  have h_sub_ball : Ioo (t - δ') (t + δ') ⊆ f ⁻¹' (Ioi 0) := by
    intro s hs; apply hδ_sub; rw [Metric.mem_ball, Real.dist_eq]
    simp only [Set.mem_Ioo] at hs; rw [abs_lt]
    constructor <;> nlinarith
  have h_vol : 0 < volume (Ioo (t - δ') (t + δ')) := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
  have h_zero : ∀ᵐ s ∂(volume.restrict (Ioo (t - δ') (t + δ'))), f s = 0 :=
    ae_restrict_of_ae_restrict_of_subset h_sub_ab h_ae
  have h_ne_zero : volume.restrict (Ioo (t - δ') (t + δ')) ≠ 0 := by
    intro h; rw [Measure.restrict_eq_zero] at h; exact absurd h (ne_of_gt h_vol)
  haveI : (ae (volume.restrict (Ioo (t - δ') (t + δ')))).NeBot := ae_neBot.mpr h_ne_zero
  obtain ⟨s, hs_zero, hs_mem⟩ := (h_zero.and (ae_restrict_mem measurableSet_Ioo)).exists
  exact ne_of_gt (h_sub_ball hs_mem) hs_zero

/-! ## Step 4: From L² vanishing to pointwise a.e. equality -/

/-- If ∫ ‖f(u) − g(u)‖₊² du = 0 (as ENNReal) and f, g are measurable,
    then f(u) = g(u) for a.e. u. -/
theorem ae_eq_of_lintegral_nnnorm_rpow_zero {f g : ℝ → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∫⁻ u, ‖f u - g u‖₊ ^ (2 : ℝ) ∂volume = 0) :
    ∀ᵐ u ∂volume, f u = g u := by
  have hmeas : Measurable (fun u => (‖f u - g u‖₊ : ENNReal) ^ (2 : ℝ)) :=
    (hf.sub hg).nnnorm.coe_nnreal_ennreal.pow_const 2
  have h_ae := (lintegral_eq_zero_iff hmeas).mp h
  filter_upwards [h_ae] with u hu
  simp only [Pi.zero_apply] at hu
  have : (‖f u - g u‖₊ : ENNReal) = 0 := by
    by_contra hx
    exact absurd hu (ne_of_gt (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hx)
      (by norm_num : (0 : ℝ) ≤ 2)))
  rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero, sub_eq_zero] at this

/-! ## Steps 3–5: Constructing translation invariance from vanishing energy -/

/-- On the overlap I ∩ (· − t)⁻¹(I), the zero extension agrees with the original.
    If zeroExtend(1_B, I)(u) = zeroExtend(1_B, I)(u−t) a.e. on ℝ,
    then 1_B(u) = 1_B(u−t) a.e. on I ∩ (·−t)⁻¹(I). -/
theorem indicator_ae_eq_on_overlap {B : Set ℝ} {L t : ℝ}
    (h_ae : ∀ᵐ u ∂volume,
      zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) u =
      zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) (u - t)) :
    ∀ᵐ u ∂(volume.restrict (logInterval L ∩ preimage (· - t) (logInterval L))),
      B.indicator (1 : ℝ → ℝ) u = B.indicator (1 : ℝ → ℝ) (u - t) := by
  have hI_meas : MeasurableSet (logInterval L) := measurableSet_Ioo
  rw [ae_restrict_iff' (hI_meas.inter (hI_meas.preimage (measurable_sub_const t)))]
  filter_upwards [h_ae] with u hu hu_mem
  have hu_I : u ∈ logInterval L := hu_mem.1
  have hut_I : u - t ∈ logInterval L := hu_mem.2
  have h_eq_C : B.indicator (1 : ℝ → ℂ) u = B.indicator (1 : ℝ → ℂ) (u - t) := by
    have h1 := zeroExtend_apply_mem (G := B.indicator (1 : ℝ → ℂ)) hu_I
    have h2 := zeroExtend_apply_mem (G := B.indicator (1 : ℝ → ℂ)) hut_I
    rw [← h1, ← h2]; exact hu
  by_cases hu_B : u ∈ B <;> by_cases hut_B : u - t ∈ B
  · simp [indicator_of_mem hu_B, indicator_of_mem hut_B]
  · exfalso; simp [indicator_of_mem hu_B, indicator_of_notMem hut_B] at h_eq_C
  · exfalso; simp [indicator_of_notMem hu_B, indicator_of_mem hut_B] at h_eq_C
  · simp [indicator_of_notMem hu_B, indicator_of_notMem hut_B]

/-! ## Main theorem: Lemma 7 -/

/-- **Lemma 7** (Indicator-energy criterion): If E_λ(1_B) = 0, then
    m(B) = 0 or m(I \ B) = 0.

    Reference: lamportform.tex, Section 6.1, Lemma 7, lines 647–696. -/
theorem energyForm_indicator_null_or_conull
    {cutoffLambda : ℝ} {B : Set ℝ} (hLam : 1 < cutoffLambda)
    (hB_meas : MeasurableSet B) (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (h_energy : energyForm cutoffLambda (B.indicator (1 : ℝ → ℂ)) = 0) :
    volume B = 0 ∨ volume (logInterval (Real.log cutoffLambda) \ B) = 0 := by
  set L := Real.log cutoffLambda
  set I := logInterval L
  set G := B.indicator (1 : ℝ → ℂ)
  set φ := zeroExtend G I
  have hL_pos : 0 < L := Real.log_pos hLam
  -- Measurability of G
  have hG_meas : Measurable G := measurable_const.indicator hB_meas
  -- Step 1: archimedean integral = 0
  have h_arch := archEnergy_eq_zero_of_energyForm_eq_zero h_energy
  -- Step 2: weighted integrand = 0 a.e. on (0, 2L)
  -- archEnergyIntegrand is measurable (product of continuous weight and measurable integral)
  have h_integrand_meas : Measurable (archEnergyIntegrand G L) := by
    unfold archEnergyIntegrand archWeight
    apply Measurable.mul
    · exact measurable_coe_nnreal_ennreal.comp
        (measurable_real_toNNReal.comp
          ((Real.continuous_exp.measurable.comp (measurable_id.div_const 2)).div
            (measurable_const.mul Real.measurable_sinh)))
    · exact measurable_archEnergyIntegrand hG_meas L
  have h_integrand_ae : ∀ᵐ t ∂(volume.restrict (Ioo 0 (2 * L))),
      archEnergyIntegrand G L t = 0 := by
    unfold archEnergyIntegral at h_arch
    exact (lintegral_eq_zero_iff h_integrand_meas).mp h_arch
  -- Step 2b: factor out w(t) > 0 to get ∫ ‖φ − S_t φ‖² = 0 a.e. t
  have h_norm_ae : ∀ᵐ t ∂(volume.restrict (Ioo 0 (2 * L))),
      ∫⁻ u, ‖φ u - translationOp t φ u‖₊ ^ (2 : ℝ) ∂volume = 0 := by
    filter_upwards [h_integrand_ae, ae_restrict_mem measurableSet_Ioo]
      with t h_zero ht
    exact translationOp_normSq_zero_of_weighted_zero ht.1 h_zero
  -- Measurability of φ (needed for axiom and later steps)
  have hφ_meas : Measurable φ := hG_meas.indicator (measurableSet_logInterval L)
  -- Finite L² norm of φ (indicator of bounded set has finite L² norm)
  have hφ_sq : ∫⁻ u, ‖φ u‖₊ ^ (2 : ℝ) ∂volume < ⊤ := by
    -- φ = zeroExtend (B.indicator 1) I, so ‖φ u‖ ≤ 1 and φ = 0 outside I
    have h_le : ∀ u, (‖φ u‖₊ : ENNReal) ^ (2 : ℝ) ≤ I.indicator 1 u := by
      intro u; simp only [φ, zeroExtend, Set.indicator]
      split_ifs with hI
      · -- u ∈ I: ‖G u‖₊ ^ 2 ≤ 1 since G = B.indicator 1
        simp only [Pi.one_apply, G, Set.indicator]
        split_ifs with hB
        · simp [nnnorm_one]
        · simp
      · simp
    calc ∫⁻ u, ‖φ u‖₊ ^ (2 : ℝ) ∂volume
        ≤ ∫⁻ u, I.indicator 1 u ∂volume := lintegral_mono h_le
      _ = volume I := lintegral_indicator_one (measurableSet_logInterval L)
      _ < ⊤ := measure_Ioo_lt_top
  -- Step 3: continuity upgrade (via axiom) — for ALL t ∈ (0, 2L)
  have h_norm_all : ∀ t ∈ Ioo 0 (2 * L),
      ∫⁻ u, ‖φ u - translationOp t φ u‖₊ ^ (2 : ℝ) ∂volume = 0 :=
    continuous_ae_zero_imp_zero
      (translation_norm_sq_continuous φ hφ_meas hφ_sq) h_norm_ae
  -- Step 4: for each t, get pointwise a.e. equality → indicator invariance
  have h_ae_shift : ∀ t, 0 < t → t < 2 * L →
      ∀ᵐ u ∂(volume.restrict (I ∩ preimage (· - t) I)),
        B.indicator (1 : ℝ → ℝ) u = B.indicator (1 : ℝ → ℝ) (u - t) := by
    intro t ht_pos ht_bound
    have h_zero := h_norm_all t ⟨ht_pos, ht_bound⟩
    -- φ(u) = φ(u-t) a.e. (from L² vanishing + measurability)
    have h_ae_eq := ae_eq_of_lintegral_nnnorm_rpow_zero hφ_meas
      (hφ_meas.comp (measurable_sub_const t)) h_zero
    -- Convert to translationOp form
    have h_ae_trans : ∀ᵐ u ∂volume, φ u = φ (u - t) := h_ae_eq
    exact indicator_ae_eq_on_overlap h_ae_trans
  -- Step 5: Apply null_or_conull_of_translation_invariant
  exact null_or_conull_of_translation_invariant {
    ε_pos := by linarith
    B_measurable := hB_meas
    B_subset := hB_sub
    I_open := ⟨-L, L, by linarith, rfl⟩
    ae_shift := h_ae_shift
  }

/-! ## Energy positivity for constant function (Remark 4) -/

/-- The symmetric difference of I = Ioo (-L) L with its translate
    Ioo (-L+s) (L+s) has measure 2s for 0 < s < 2L.

    Reference: lamportform.tex, Remark 4, Step 1. -/
theorem symm_diff_logInterval_measure {L s : ℝ} (hs : 0 < s) (hs2L : s < 2 * L) :
    volume (symmDiff (logInterval L) (Set.preimage (· - s) (logInterval L))) =
      ENNReal.ofReal (2 * s) := by
  unfold logInterval
  have h_shift : Set.preimage (· - s) (Ioo (-L) L) = Ioo (-L + s) (L + s) := by
    ext u; simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [h_shift]
  have hLs : -L + s < L := by linarith
  -- A \ B = Ioc(-L, -L+s), B \ A = Ico(L, L+s)
  have h_diff1 : Ioo (-L) L \ Ioo (-L + s) (L + s) = Ioc (-L) (-L + s) := by
    ext u; simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_Ioc, not_and_or, not_lt]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
      · exact ⟨h1, h3⟩
      · linarith
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by linarith⟩, Or.inl h2⟩
  have h_diff2 : Ioo (-L + s) (L + s) \ Ioo (-L) L = Ico L (L + s) := by
    ext u; simp only [Set.mem_diff, Set.mem_Ioo, Set.mem_Ico, not_and_or, not_lt]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
      · exact absurd (lt_of_lt_of_le h1 h3) (by linarith)
      · exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, h2⟩, Or.inr h1⟩
  rw [symmDiff_def, h_diff1, h_diff2]; simp only [sup_eq_union]
  have h_disj : Disjoint (Ioc (-L) (-L + s)) (Ico L (L + s)) :=
    Set.disjoint_left.mpr fun u hu1 hu2 => by
      simp only [Set.mem_Ioc] at hu1; simp only [Set.mem_Ico] at hu2; linarith
  rw [measure_union h_disj measurableSet_Ico, Real.volume_Ioc, Real.volume_Ico]
  rw [show -L + s - -L = s from by ring, show L + s - L = s from by ring]
  rw [← ENNReal.ofReal_add (le_of_lt hs) (le_of_lt hs)]
  ring_nf

private theorem inner_norm_sq_pos {L t : ℝ} (hL : 0 < L) (hLt : L < t) :
    0 < ∫⁻ u, (‖zeroExtend (fun _ => (1 : ℂ)) (logInterval L) u -
         translationOp t (zeroExtend (fun _ => (1 : ℂ)) (logInterval L)) u‖₊ : ENNReal)
          ^ (2 : ℝ) ∂volume := by
  -- The integrand is 1 on Ioo (-L) 0 (a set of positive measure)
  have h_eq_one : ∀ u ∈ Ioo (-L) (0 : ℝ),
      (‖zeroExtend (fun _ => (1 : ℂ)) (logInterval L) u -
       translationOp t (zeroExtend (fun _ => (1 : ℂ)) (logInterval L)) u‖₊ : ENNReal)
        ^ (2 : ℝ) = 1 := by
    intro u hu
    have hu_I : u ∈ logInterval L := Ioo_subset_Ioo_right (by linarith) hu
    have hut_not_I : u - t ∉ logInterval L := by
      unfold logInterval; intro h; exact absurd h.1 (by linarith [hu.2])
    simp only [translationOp, zeroExtend,
      Set.indicator_of_mem hu_I, Set.indicator_of_notMem hut_not_I]
    norm_num
  calc (0 : ENNReal) < ENNReal.ofReal L := ENNReal.ofReal_pos.mpr hL
    _ = volume (Ioo (-L) 0) := by rw [Real.volume_Ioo]; ring_nf
    _ = ∫⁻ _ in Ioo (-L) 0, 1 ∂volume := by simp
    _ = ∫⁻ u in Ioo (-L) 0,
          (‖zeroExtend (fun _ => (1 : ℂ)) (logInterval L) u -
           translationOp t (zeroExtend (fun _ => (1 : ℂ)) (logInterval L)) u‖₊ : ENNReal)
            ^ (2 : ℝ) ∂volume :=
        (setLIntegral_congr_fun measurableSet_Ioo fun u hu => (h_eq_one u hu).symm)
    _ ≤ ∫⁻ u,
          (‖zeroExtend (fun _ => (1 : ℂ)) (logInterval L) u -
           translationOp t (zeroExtend (fun _ => (1 : ℂ)) (logInterval L)) u‖₊ : ENNReal)
            ^ (2 : ℝ) ∂volume :=
        lintegral_mono' Measure.restrict_le_self le_rfl

/-- **E_λ(1) > 0**: The energy of the constant function 1 on I is strictly positive.

    For 0 < t < 2L, ‖1̃ − S_t 1̃‖² = m(I △ (I+t)) = 2t > 0.
    Since w(t) > 0, the archimedean integral is positive.

    Reference: lamportform.tex, Remark 4, Step 1, lines 706–713. -/
theorem energyForm_constant_pos {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    0 < energyForm cutoffLambda (fun _ => (1 : ℂ)) := by
  unfold energyForm
  suffices h : 0 < archEnergyIntegral (fun _ => (1 : ℂ)) (Real.log cutoffLambda) by
    exact lt_of_lt_of_le h le_self_add
  have hL_pos : 0 < Real.log cutoffLambda := Real.log_pos hLam
  set L := Real.log cutoffLambda
  -- Measurability of the energy integrand
  have h_integrand_meas : Measurable (archEnergyIntegrand (fun _ => (1 : ℂ)) L) := by
    unfold archEnergyIntegrand archWeight
    apply Measurable.mul
    · exact measurable_coe_nnreal_ennreal.comp
        (measurable_real_toNNReal.comp
          ((Real.continuous_exp.measurable.comp (measurable_id.div_const 2)).div
            (measurable_const.mul Real.measurable_sinh)))
    · exact measurable_archEnergyIntegrand measurable_const _
  -- Use setLIntegral_pos_iff: integral > 0 iff support has positive measure
  unfold archEnergyIntegral
  rw [setLIntegral_pos_iff h_integrand_meas]
  -- The support of archEnergyIntegrand ∩ Ioo 0 (2L) has positive measure
  -- because archEnergyIntegrand ≠ 0 on Ioo L (2L)
  have h_support_sub : Ioo L (2 * L) ⊆
      Function.support (archEnergyIntegrand (fun _ => (1 : ℂ)) L) ∩ Ioo 0 (2 * L) := by
    intro t ht
    refine ⟨?_, ⟨by linarith [ht.1], ht.2⟩⟩
    rw [Function.mem_support]
    unfold archEnergyIntegrand
    apply mul_ne_zero
    · exact ENNReal.coe_ne_zero.mpr (ne_of_gt
        (Real.toNNReal_pos.mpr (archWeight_pos (by linarith [ht.1]))))
    · exact ne_of_gt (inner_norm_sq_pos hL_pos ht.1)
  calc (0 : ENNReal)
      < ENNReal.ofReal L := ENNReal.ofReal_pos.mpr hL_pos
    _ = volume (Ioo L (2 * L)) := by rw [Real.volume_Ioo]; ring_nf
    _ ≤ volume (Function.support (archEnergyIntegrand (fun _ => (1 : ℂ)) L) ∩ Ioo 0 (2 * L)) :=
        measure_mono h_support_sub

/-- **Remark 4 (sharpened)**: If E_λ(1_B) = 0, then m(B) = 0.

    The conull alternative m(I \ B) = 0 is excluded because it would give
    E_λ(1_B) = E_λ(1) > 0. Contradiction with E_λ(1_B) = 0.

    Reference: lamportform.tex, Remark 4, lines 698–723. -/
theorem energyForm_indicator_null
    {cutoffLambda : ℝ} {B : Set ℝ} (hLam : 1 < cutoffLambda)
    (hB_meas : MeasurableSet B) (hB_sub : B ⊆ logInterval (Real.log cutoffLambda))
    (h_energy : energyForm cutoffLambda (B.indicator (1 : ℝ → ℂ)) = 0) :
    volume B = 0 := by
  rcases energyForm_indicator_null_or_conull hLam hB_meas hB_sub h_energy with h | h
  · exact h
  · -- m(I \ B) = 0 → 1_B = 1 a.e. on I → E_λ(1_B) = E_λ(1) > 0, contradiction
    exfalso
    have h_pos := energyForm_constant_pos hLam
    set L := Real.log cutoffLambda
    -- Zero-extensions agree a.e. (differ only on I \ B, which is null)
    have h_ze_ae : zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) =ᵐ[volume]
        zeroExtend (fun _ => (1 : ℂ)) (logInterval L) := by
      rw [Filter.EventuallyEq, ae_iff]
      have h_sub : {u | zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) u ≠
                        zeroExtend (fun _ => (1 : ℂ)) (logInterval L) u} ⊆
                   logInterval L \ B := by
        intro u hu
        constructor
        · by_contra h_nI
          exact hu (by simp [zeroExtend, Set.indicator_of_notMem h_nI])
        · intro h_B
          exact hu (by simp [zeroExtend, Set.indicator_of_mem (hB_sub h_B),
            Set.indicator_of_mem h_B])
      exact measure_mono_null h_sub h
    -- Inner lintegrals agree for each t
    have h_inner : ∀ t : ℝ,
        (∫⁻ u, ‖zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) u -
               translationOp t (zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L)) u‖₊
                 ^ (2 : ℝ) ∂volume) =
        (∫⁻ u, ‖zeroExtend (fun _ => (1 : ℂ)) (logInterval L) u -
               translationOp t (zeroExtend (fun _ => (1 : ℂ)) (logInterval L)) u‖₊
                 ^ (2 : ℝ) ∂volume) := by
      intro t; apply lintegral_congr_ae
      have h_shift : zeroExtend (B.indicator (1 : ℝ → ℂ)) (logInterval L) ∘ (· - t) =ᵐ[volume]
          zeroExtend (fun _ => (1 : ℂ)) (logInterval L) ∘ (· - t) :=
        (measurePreserving_sub_const t).quasiMeasurePreserving.ae_eq_comp h_ze_ae
      filter_upwards [h_ze_ae, h_shift] with u hu1 hu2
      simp only [translationOp, Function.comp_def] at hu2 ⊢; rw [hu1, hu2]
    -- Energy forms are equal
    have h_eq : energyForm cutoffLambda (B.indicator (1 : ℝ → ℂ)) =
                energyForm cutoffLambda (fun _ => (1 : ℂ)) := by
      simp only [energyForm, archEnergyIntegral]
      congr 1
      · apply lintegral_congr; intro t
        simp only [archEnergyIntegrand]; congr 1; exact h_inner t
      · apply Finset.sum_congr rfl; intro p _
        simp only [totalPrimeEnergy]; apply Finset.sum_congr rfl; intro m _
        simp only [primeEnergyTerm]; congr 1; exact h_inner _
    rw [h_eq] at h_energy
    exact absurd h_energy (ne_of_gt h_pos)

end

end ConnesLean
