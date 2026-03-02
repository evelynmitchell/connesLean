/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cross-Term Vanishing — Proposition 10, Steps 9–10

Reference: lamportform.tex, Proposition 10, Steps 9–10 (lines 1400–1425).

From the inner integral equality (Stage 6D-ii), we extract pointwise norm
equality a.e., then on the overlap region where both u and u-t are in I,
the LHS vanishes, forcing `1_B(u) = 1_B(u-t)` a.e. This gives translation
invariance of `1_B`, and by the null-or-conull theorem (Stage 4), either
`volume B = 0` or `volume (I \ B) = 0`.

## Main results

- `nnnorm_sq_indicator_ae_eq`: pointwise norm equality a.e. for each t ∈ (0,2L)
- `indicator_B_ae_invariant`: `1_B(u) = 1_B(u-t)` a.e. on the overlap
- `indicator_translation_invariant_of_split`: constructs `IndicatorTranslationInvariant`
- `invariant_ideal_null_or_conull`: `volume B = 0 ∨ volume (I \ B) = 0`
-/

import ConnesLean.Stage6.EnergyEquality

/-!
# Cross-Term Vanishing

From the energy form equality + norm inequality, the inner integrals must
agree pointwise. On the overlap region where both u and u-t lie in I,
this forces `1_B(u) = 1_B(u-t)` a.e., giving translation invariance.
The null-or-conull theorem then concludes.

Reference: lamportform.tex, Proposition 10, Steps 9–10 (lines 1400–1425).
-/

namespace ConnesLean

open MeasureTheory Set Real Filter ENNReal

noncomputable section

/-! ## Section 1: Pointwise norm equality a.e. -/

/-- **Pointwise norm equality a.e.** For each `t ∈ (0, 2L)`:
    `‖ze(1)(u) - ze(1)(u-t)‖₊² = ‖ze(1_B)(u) - ze(1_B)(u-t)‖₊²
                                  + ‖ze(1_{I\B})(u) - ze(1_{I\B})(u-t)‖₊²`
    a.e. in `u`.

    Proof: apply `ae_eq_of_ae_le_of_lintegral_le` with the pointwise `≤`
    from `nnnorm_sq_indicator_le` and the integral equality from
    `inner_integral_indicator_everywhere_eq`.

    Reference: lamportform.tex, Proposition 10, Step 9 (line 1411). -/
theorem nnnorm_sq_indicator_ae_eq {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda)
    {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.log cutoffLambda)) :
    ∀ᵐ u ∂volume,
    (‖zeroExtend (1 : ℝ → ℂ) (logInterval (Real.log cutoffLambda)) u -
      zeroExtend (1 : ℝ → ℂ) (logInterval (Real.log cutoffLambda)) (u - t)‖₊
        : ENNReal) ^ (2 : ℝ) =
    (‖zeroExtend (inv.B.indicator (1 : ℝ → ℂ))
        (logInterval (Real.log cutoffLambda)) u -
      zeroExtend (inv.B.indicator (1 : ℝ → ℂ))
        (logInterval (Real.log cutoffLambda)) (u - t)‖₊
        : ENNReal) ^ (2 : ℝ) +
    (‖zeroExtend ((logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ))
        (logInterval (Real.log cutoffLambda)) u -
      zeroExtend ((logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ))
        (logInterval (Real.log cutoffLambda)) (u - t)‖₊
        : ENNReal) ^ (2 : ℝ) := by
  set L := Real.log cutoffLambda
  set I := logInterval L
  -- Pointwise ≤
  have h_le : ∀ᵐ u ∂volume,
      (‖zeroExtend (1 : ℝ → ℂ) I u -
        zeroExtend (1 : ℝ → ℂ) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) ≤
      (‖zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I u -
        zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) +
      (‖zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I u -
        zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal)
          ^ (2 : ℝ) :=
    Filter.Eventually.of_forall fun u => nnnorm_sq_indicator_le inv.B_subset u t
  -- ∫ f ≠ ⊤
  have h_fin : ∫⁻ u, (‖zeroExtend (1 : ℝ → ℂ) I u -
      zeroExtend (1 : ℝ → ℂ) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) ≠ ⊤ := by
    rw [show (fun u => (‖zeroExtend (1 : ℝ → ℂ) I u -
        zeroExtend (1 : ℝ → ℂ) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ)) =
      (fun u => (‖zeroExtend (1 : ℝ → ℂ) I u -
        translationOp t (zeroExtend (1 : ℝ → ℂ) I) u‖₊ : ENNReal) ^ (2 : ℝ))
      by ext u; simp [translationOp_apply]]
    exact ne_top_of_lt (inner_integral_one_lt_top L t)
  -- g is AEMeasurable
  have hBm : Measurable (zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I) :=
    (measurable_const.indicator inv.B_measurable).indicator (measurableSet_logInterval L)
  have hDm : Measurable (zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I) :=
    (measurable_const.indicator
      ((measurableSet_logInterval L).diff inv.B_measurable)).indicator
      (measurableSet_logInterval L)
  have h_g_meas : AEMeasurable (fun u =>
      (‖zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I u -
        zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) +
      (‖zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I u -
        zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal)
          ^ (2 : ℝ)) volume :=
    ((hBm.sub (hBm.comp (measurable_id.sub measurable_const)))
      |>.nnnorm.coe_nnreal_ennreal.pow_const _ |>.add
    ((hDm.sub (hDm.comp (measurable_id.sub measurable_const)))
      |>.nnnorm.coe_nnreal_ennreal.pow_const _)).aemeasurable
  -- ∫ g ≤ ∫ f (from inner integral equality)
  -- Define the component functions explicitly for lintegral_add_left
  set fB : ℝ → ENNReal := fun u =>
      (‖zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I u -
        zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ)
  set fD : ℝ → ENNReal := fun u =>
      (‖zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I u -
        zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ)
  have hfB_meas : Measurable fB :=
    (hBm.sub (hBm.comp (measurable_id.sub measurable_const)))
      |>.nnnorm.coe_nnreal_ennreal.pow_const _
  have h_int_le : ∫⁻ u, (fB u + fD u) ≤
      ∫⁻ u, (‖zeroExtend (1 : ℝ → ℂ) I u -
        zeroExtend (1 : ℝ → ℂ) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) := by
    rw [lintegral_add_left hfB_meas]
    -- Now goal: ∫ fB + ∫ fD ≤ ∫ h
    -- Use inner_integral_indicator_everywhere_eq
    have h_eq := inner_integral_indicator_everywhere_eq hLam inv t ht
    -- h_eq : innerIntegral 1 L t = innerIntegral B L t + innerIntegral D L t
    -- innerIntegral uses translationOp, convert via simp
    change innerIntegral (inv.B.indicator 1) L t +
      innerIntegral ((I \ inv.B).indicator 1) L t ≤
      innerIntegral 1 L t
    rw [h_eq]
  exact ae_eq_of_ae_le_of_lintegral_le h_le h_fin h_g_meas h_int_le

/-! ## Section 2: Indicator ae invariance on overlap -/

/-- **Indicator ae invariance on overlap.** For each `t ∈ (0, 2L)`,
    `1_B(u) = 1_B(u-t)` a.e. on the overlap `I ∩ preimage (·-t) I`.

    On the overlap, `ze(1)(u) = 1` and `ze(1)(u-t) = 1`, so the LHS norm
    vanishes. The pointwise equality then forces both RHS norms to vanish,
    giving `ze(1_B)(u) = ze(1_B)(u-t)`, which unfolds to `1_B(u) = 1_B(u-t)`.

    Reference: lamportform.tex, Proposition 10, Step 10 (line 1418). -/
theorem indicator_B_ae_invariant {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda)
    {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.log cutoffLambda)) :
    ∀ᵐ u ∂(volume.restrict
      (logInterval (Real.log cutoffLambda) ∩
       preimage (· - t) (logInterval (Real.log cutoffLambda)))),
    inv.B.indicator (1 : ℝ → ℝ) u = inv.B.indicator (1 : ℝ → ℝ) (u - t) := by
  set L := Real.log cutoffLambda
  set I := logInterval L
  -- Get pointwise norm equality a.e. on volume
  have h_ae := nnnorm_sq_indicator_ae_eq hLam inv ht
  -- Restrict to the overlap
  have h_measI := measurableSet_logInterval L
  have h_ae' : ∀ᵐ u ∂(volume.restrict (I ∩ preimage (· - t) I)),
      (‖zeroExtend (1 : ℝ → ℂ) I u -
        zeroExtend (1 : ℝ → ℂ) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) =
      (‖zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I u -
        zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) +
      (‖zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I u -
        zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I (u - t)‖₊ : ENNReal)
          ^ (2 : ℝ) :=
    ae_restrict_of_ae h_ae
  have h_mem : ∀ᵐ u ∂(volume.restrict (I ∩ preimage (· - t) I)),
      u ∈ I ∩ preimage (· - t) I :=
    ae_restrict_mem (h_measI.inter (h_measI.preimage (measurable_id.sub measurable_const)))
  filter_upwards [h_ae', h_mem] with u h_eq hu_mem
  have hu_I := hu_mem.1
  have hu_t_I : u - t ∈ I := hu_mem.2
  -- On overlap: ze(1)(u) = 1 and ze(1)(u-t) = 1, so LHS = 0
  have h1_u : zeroExtend (1 : ℝ → ℂ) I u = 1 := zeroExtend_apply_mem hu_I
  have h1_ut : zeroExtend (1 : ℝ → ℂ) I (u - t) = 1 := zeroExtend_apply_mem hu_t_I
  have h_lhs_zero : (‖zeroExtend (1 : ℝ → ℂ) I u -
      zeroExtend (1 : ℝ → ℂ) I (u - t)‖₊ : ENNReal) ^ (2 : ℝ) = 0 := by
    simp [h1_u, h1_ut]
  -- RHS = 0 from equality + LHS = 0
  rw [h_lhs_zero] at h_eq
  have h_both_zero := add_eq_zero.mp h_eq.symm
  -- Extract ze(1_B)(u) = ze(1_B)(u-t) from first component = 0
  have h_B_eq : zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I u =
      zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I (u - t) := by
    have h0 := h_both_zero.1
    rcases ENNReal.rpow_eq_zero_iff.mp h0 with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [ENNReal.coe_eq_zero, nnnorm_eq_zero, sub_eq_zero] at h1; exact h1
    · norm_num at h2
  -- Unfold ze on overlap
  rw [zeroExtend_apply_mem hu_I, zeroExtend_apply_mem hu_t_I] at h_B_eq
  -- Convert ℂ indicator equality to ℝ indicator equality
  by_cases hB : u ∈ inv.B <;> by_cases hBt : (u - t) ∈ inv.B
  · simp [indicator_of_mem hB, indicator_of_mem hBt]
  · exfalso; simp [indicator_of_mem hB, indicator_of_notMem hBt] at h_B_eq
  · exfalso; simp [indicator_of_notMem hB, indicator_of_mem hBt] at h_B_eq
  · simp [indicator_of_notMem hB, indicator_of_notMem hBt]

/-! ## Section 3: Translation invariance construction -/

/-- **Translation invariance of `1_B`.** Constructs the
    `IndicatorTranslationInvariant` hypothesis for `inv.B` on `I = (-L, L)`
    with `ε = 2L`.

    Reference: lamportform.tex, Proposition 10, Step 10 (line 1420). -/
theorem indicator_translation_invariant_of_split {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    IndicatorTranslationInvariant inv.B
      (logInterval (Real.log cutoffLambda))
      (2 * Real.log cutoffLambda) where
  ε_pos := by linarith [Real.log_pos hLam]
  B_measurable := inv.B_measurable
  B_subset := inv.B_subset
  I_open := ⟨-Real.log cutoffLambda, Real.log cutoffLambda,
    by linarith [Real.log_pos hLam], rfl⟩
  ae_shift := fun t ht_pos ht_bound =>
    indicator_B_ae_invariant hLam inv ⟨ht_pos, ht_bound⟩

/-! ## Section 4: Null or conull conclusion -/

/-- **Invariant ideal is null or conull.** From the translation invariance
    of `1_B`, apply the null-or-conull theorem: either `volume B = 0`
    or `volume (I \ B) = 0`.

    Reference: lamportform.tex, Proposition 10, Step 10 (line 1425). -/
theorem invariant_ideal_null_or_conull {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    volume inv.B = 0 ∨
    volume (logInterval (Real.log cutoffLambda) \ inv.B) = 0 :=
  null_or_conull_of_translation_invariant
    (indicator_translation_invariant_of_split hLam inv)

/-! ## Section 5: Soundness tests -/

-- Test 1: invariant_ideal_null_or_conull composes with EnergyFormSplit
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    volume inv.B = 0 ∨
    volume (logInterval (Real.log cutoffLambda) \ inv.B) = 0 :=
  invariant_ideal_null_or_conull hLam inv

-- Test 2: indicator_translation_invariant_of_split produces the right type
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    IndicatorTranslationInvariant inv.B
      (logInterval (Real.log cutoffLambda))
      (2 * Real.log cutoffLambda) :=
  indicator_translation_invariant_of_split hLam inv

-- Test 3: nnnorm_sq_indicator_ae_eq composes with inner_integral_indicator_everywhere_eq
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda)
    {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.log cutoffLambda)) :
    ∀ᵐ u ∂(volume.restrict
      (logInterval (Real.log cutoffLambda) ∩
       preimage (· - t) (logInterval (Real.log cutoffLambda)))),
    inv.B.indicator (1 : ℝ → ℝ) u = inv.B.indicator (1 : ℝ → ℝ) (u - t) :=
  indicator_B_ae_invariant hLam inv ht

end

end ConnesLean
