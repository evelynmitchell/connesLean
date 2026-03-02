/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Energy Equality — Proposition 10, Steps 8–9

Reference: lamportform.tex, Proposition 10, Steps 8–9 (lines 1391–1425).

The energy form equality `E_λ(1) = E_λ(1_B) + E_λ(1_{I\B})` (from Stage 6C),
combined with the norm inequality `E_λ(1) ≤ E_λ(1_B) + E_λ(1_{I\B})` (from 6D-i),
forces the archimedean energy integrands to agree a.e. This propagates to
pointwise equality of the inner integrals on `(0, 2L)` via weight cancellation
and continuity.

## Main results

- `archEnergyIntegral_indicator_eq`: `arch(1) = arch(B) + arch(Bc)`
- `archEnergyIntegrand_indicator_ae_eq`: integrands agree a.e. on `(0, 2L)`
- `inner_integral_indicator_ae_eq`: inner integrals agree a.e. on `(0, 2L)`
- `inner_integral_indicator_everywhere_eq`: inner integrals agree for all `t ∈ (0, 2L)`
-/

import ConnesLean.Stage6.NormInequality

/-!
# Energy Equality for Disjoint Indicators

Establishes that the energy form equality from Stage 6C, combined with the
norm inequality from Stage 6D-i, forces component-wise equality of the
archimedean energy integrands, and by continuity, of the inner integrals
everywhere on `(0, 2L)`.

Reference: lamportform.tex, Proposition 10, Steps 8–9 (lines 1391–1425).
-/

namespace ConnesLean

open MeasureTheory Set Real Filter ENNReal

noncomputable section

/-! ## Section 1: ENNReal cancellation helper -/

/-- In ENNReal, if `a + b = c + d`, `a ≤ c`, `b ≤ d`, and the sum is finite,
    then `a = c`. -/
private theorem ennreal_add_cancel {a b c d : ENNReal}
    (h_eq : a + b = c + d) (h_ac : a ≤ c) (h_bd : b ≤ d)
    (h_fin : a + b ≠ ⊤) : a = c := by
  apply le_antisymm h_ac
  have h_d_fin : d ≠ ⊤ := by
    rw [h_eq] at h_fin; exact (ENNReal.add_ne_top.mp h_fin).2
  have h1 : a + b ≤ a + d := add_le_add_right h_bd a
  rw [h_eq] at h1
  exact (ENNReal.add_le_add_iff_right h_d_fin).mp h1

/-! ## Section 2: Archimedean energy integral equality -/

/-- **Archimedean energy integral equality.** The archimedean energy of the
    constant function equals the sum of energies of complementary indicators.

    Proof: the full energy form equality (Stage 6C) + component-wise inequalities
    (Stage 6D-i) + ENNReal cancellation.

    Reference: lamportform.tex, Proposition 10, Step 8 (line 1391). -/
theorem archEnergyIntegral_indicator_eq {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    archEnergyIntegral (1 : ℝ → ℂ) (Real.log cutoffLambda) =
    archEnergyIntegral (inv.B.indicator (1 : ℝ → ℂ)) (Real.log cutoffLambda) +
    archEnergyIntegral
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ))
      (Real.log cutoffLambda) := by
  set L := Real.log cutoffLambda
  set I := logInterval L
  -- Energy form equality and finiteness
  have h_eq := (splitting_applied_to_constant hLam inv).2.2
  have h_fin : energyForm cutoffLambda (1 : ℝ → ℂ) ≠ ⊤ :=
    constant_in_formDomain hLam
  -- Archimedean component inequality
  have h_arch_le : archEnergyIntegral (1 : ℝ → ℂ) L ≤
      archEnergyIntegral (inv.B.indicator 1) L +
      archEnergyIntegral ((I \ inv.B).indicator 1) L := by
    unfold archEnergyIntegral
    calc ∫⁻ t in Ioo 0 (2 * L), archEnergyIntegrand (1 : ℝ → ℂ) L t
        ≤ ∫⁻ t in Ioo 0 (2 * L),
          (archEnergyIntegrand (inv.B.indicator 1) L t +
           archEnergyIntegrand ((I \ inv.B).indicator 1) L t) :=
        lintegral_mono (fun t =>
          archEnergyIntegrand_indicator_le inv.B_subset inv.B_measurable t)
      _ = _ := lintegral_add_left
          (measurable_archWeight_toNNReal.coe_nnreal_ennreal.mul
            (measurable_archEnergyIntegrand
              (measurable_const.indicator inv.B_measurable) L)) _
  -- Prime component inequality
  have h_prime_le :
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda (1 : ℝ → ℂ) L ≤
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda (inv.B.indicator 1) L +
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda ((I \ inv.B).indicator 1) L := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro p _; unfold totalPrimeEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro m _
    exact primeEnergyTerm_indicator_le inv.B_subset inv.B_measurable p m
  -- Rearrange energy form equality into component form
  have h_rearr : archEnergyIntegral (1 : ℝ → ℂ) L +
      ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda (1 : ℝ → ℂ) L =
      (archEnergyIntegral (inv.B.indicator 1) L +
       archEnergyIntegral ((I \ inv.B).indicator 1) L) +
      (∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda (inv.B.indicator 1) L +
       ∑ p ∈ primeFinset cutoffLambda,
        totalPrimeEnergy p cutoffLambda ((I \ inv.B).indicator 1) L) := by
    have h1 : energyForm cutoffLambda (1 : ℝ → ℂ) =
        archEnergyIntegral (1 : ℝ → ℂ) L +
        ∑ p ∈ primeFinset cutoffLambda,
          totalPrimeEnergy p cutoffLambda (1 : ℝ → ℂ) L := rfl
    rw [← h1, h_eq]; unfold energyForm; rw [add_add_add_comm]
  exact ennreal_add_cancel h_rearr h_arch_le h_prime_le h_fin

/-! ## Section 3: Archimedean energy integrand ae equality -/

/-- The archimedean energy integrands agree a.e. on `(0, 2L)`:
    `archEnergyIntegrand(1, t) = archEnergyIntegrand(B, t) + archEnergyIntegrand(Bc, t)`.

    Proof: pointwise `≤` (from 6D-i) + integral equality (Theorem 1) +
    `ae_eq_of_ae_le_of_lintegral_le`.

    Reference: lamportform.tex, Proposition 10, Step 8. -/
theorem archEnergyIntegrand_indicator_ae_eq {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 (2 * Real.log cutoffLambda))),
    archEnergyIntegrand (1 : ℝ → ℂ) (Real.log cutoffLambda) t =
    archEnergyIntegrand (inv.B.indicator (1 : ℝ → ℂ)) (Real.log cutoffLambda) t +
    archEnergyIntegrand
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ))
      (Real.log cutoffLambda) t := by
  set L := Real.log cutoffLambda
  set I := logInterval L
  -- Pointwise ≤
  have h_le : ∀ᵐ t ∂(volume.restrict (Ioo 0 (2 * L))),
      archEnergyIntegrand (1 : ℝ → ℂ) L t ≤
      archEnergyIntegrand (inv.B.indicator 1) L t +
      archEnergyIntegrand ((I \ inv.B).indicator 1) L t :=
    Filter.Eventually.of_forall fun t =>
      archEnergyIntegrand_indicator_le inv.B_subset inv.B_measurable t
  -- ∫ f ≠ ⊤
  have h_fin : ∫⁻ t in Ioo 0 (2 * L),
      archEnergyIntegrand (1 : ℝ → ℂ) L t ≠ ⊤ :=
    ne_top_of_lt (archEnergyIntegral_one_lt_top (Real.log_pos hLam))
  -- g is AEMeasurable
  have h_g_meas : AEMeasurable (fun t =>
      archEnergyIntegrand (inv.B.indicator 1) L t +
      archEnergyIntegrand ((I \ inv.B).indicator 1) L t)
      (volume.restrict (Ioo 0 (2 * L))) :=
    ((measurable_archWeight_toNNReal.coe_nnreal_ennreal.mul
        (measurable_archEnergyIntegrand
          (measurable_const.indicator inv.B_measurable) L)).add
      (measurable_archWeight_toNNReal.coe_nnreal_ennreal.mul
        (measurable_archEnergyIntegrand
          (measurable_const.indicator
            ((measurableSet_logInterval L).diff inv.B_measurable)) L))).aemeasurable
  -- ∫ g ≤ ∫ f (from integral equality)
  have hBm_arch : Measurable (archEnergyIntegrand (inv.B.indicator (1 : ℝ → ℂ)) L) :=
    measurable_archWeight_toNNReal.coe_nnreal_ennreal.mul
      (measurable_archEnergyIntegrand (measurable_const.indicator inv.B_measurable) L)
  have h_int_le : ∫⁻ t in Ioo 0 (2 * L),
      (archEnergyIntegrand (inv.B.indicator 1) L t +
       archEnergyIntegrand ((I \ inv.B).indicator 1) L t) ≤
      ∫⁻ t in Ioo 0 (2 * L),
        archEnergyIntegrand (1 : ℝ → ℂ) L t := by
    rw [lintegral_add_left hBm_arch]
    exact le_of_eq (archEnergyIntegral_indicator_eq hLam inv).symm
  exact ae_eq_of_ae_le_of_lintegral_le h_le h_fin h_g_meas h_int_le

/-! ## Section 4: Inner integral definition and ae equality -/

/-- The inner L² translation integral: `∫ ‖φ̃(u) - S_t φ̃(u)‖₊² du`
    where `φ̃ = zeroExtend G I`. This is the second factor of
    `archEnergyIntegrand G L t = weight(t) * innerIntegral G L t`. -/
def innerIntegral (G : ℝ → ℂ) (L : ℝ) (t : ℝ) : ENNReal :=
  ∫⁻ u, ‖zeroExtend G (logInterval L) u -
    translationOp t (zeroExtend G (logInterval L)) u‖₊ ^ (2 : ℝ) ∂volume

/-- The inner integrals agree a.e. on `(0, 2L)`:
    `II(1, t) = II(B, t) + II(Bc, t)` for a.e. `t ∈ (0, 2L)`.

    From the integrand a.e. equality `w(t) * II(1) = w(t) * (II(B) + II(Bc))`
    by cancelling the positive weight `w(t)`.

    Reference: lamportform.tex, Proposition 10, Step 8. -/
theorem inner_integral_indicator_ae_eq {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 (2 * Real.log cutoffLambda))),
    innerIntegral (1 : ℝ → ℂ) (Real.log cutoffLambda) t =
    innerIntegral (inv.B.indicator (1 : ℝ → ℂ)) (Real.log cutoffLambda) t +
    innerIntegral
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ))
      (Real.log cutoffLambda) t := by
  set L := Real.log cutoffLambda
  have h_ae := archEnergyIntegrand_indicator_ae_eq hLam inv
  filter_upwards [h_ae, ae_restrict_mem measurableSet_Ioo] with t h_eq ht
  -- h_eq : w(t) * II(1,t) = w(t) * II(B,t) + w(t) * II(Bc,t)
  unfold archEnergyIntegrand at h_eq
  rw [← mul_add] at h_eq
  -- Cancel weight: w(t) ≠ 0 and w(t) ≠ ⊤ for t > 0
  have h_w_ne_zero : (↑(archWeight t).toNNReal : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (Real.toNNReal_pos.mpr (archWeight_pos ht.1)))
  exact (ENNReal.mul_right_inj h_w_ne_zero ENNReal.coe_ne_top).mp h_eq

/-! ## Section 5: Continuity and everywhere equality -/

/-- L² finiteness for zero-extended indicator functions: `∫ ‖φ̃‖₊² ≤ vol(I) < ⊤`.
    Since `|S.indicator 1| ≤ 1` and `zeroExtend` restricts to `I`. -/
private theorem l2_zeroExtend_indicator_lt_top {S : Set ℝ} {L : ℝ}
    (_hSm : MeasurableSet S) (_hS : S ⊆ logInterval L) :
    ∫⁻ u, ‖zeroExtend (S.indicator (1 : ℝ → ℂ)) (logInterval L) u‖₊
      ^ (2 : ℝ) ∂volume < ⊤ := by
  set I := logInterval L
  calc ∫⁻ u, ‖zeroExtend (S.indicator (1 : ℝ → ℂ)) I u‖₊ ^ (2 : ℝ) ∂volume
      ≤ ∫⁻ u, I.indicator (fun _ => (1 : ENNReal)) u ∂volume := by
        apply lintegral_mono; intro u
        simp only [zeroExtend_eq_indicator]
        by_cases hu : u ∈ I
        · simp only [indicator_of_mem hu]
          by_cases hS : u ∈ S
          · simp [indicator_of_mem hS, nnnorm_one, ENNReal.coe_one]
          · simp [indicator_of_notMem hS, nnnorm_zero, ENNReal.coe_zero,
                  ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
        · simp [indicator_of_notMem hu, nnnorm_zero, ENNReal.coe_zero,
                ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
    _ = volume I := lintegral_indicator_one (measurableSet_logInterval L)
    _ < ⊤ := measure_Ioo_lt_top

/-- L² finiteness for the zero-extended constant function. -/
private theorem l2_zeroExtend_one_lt_top (L : ℝ) :
    ∫⁻ u, ‖zeroExtend (1 : ℝ → ℂ) (logInterval L) u‖₊
      ^ (2 : ℝ) ∂volume < ⊤ := by
  set I := logInterval L
  calc ∫⁻ u, ‖zeroExtend (1 : ℝ → ℂ) I u‖₊ ^ (2 : ℝ) ∂volume
      ≤ ∫⁻ u, I.indicator (fun _ => (1 : ENNReal)) u ∂volume := by
        apply lintegral_mono; intro u
        simp only [zeroExtend_eq_indicator]
        by_cases hu : u ∈ I
        · simp [indicator_of_mem hu, nnnorm_one, ENNReal.coe_one]
        · simp [indicator_of_notMem hu, nnnorm_zero, ENNReal.coe_zero,
                ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
    _ = volume I := lintegral_indicator_one (measurableSet_logInterval L)
    _ < ⊤ := measure_Ioo_lt_top

/-- **Inner integral equality everywhere on `(0, 2L)`.** The inner integrals
    `II(1, t) = II(B, t) + II(Bc, t)` for all `t ∈ (0, 2L)`.

    Proof: each side is continuous (by `translation_norm_sq_continuous`),
    they agree a.e. (from weight cancellation), and continuous functions that
    agree a.e. on an open set agree everywhere (by `eqOn_of_ae_eq`).

    Reference: lamportform.tex, Proposition 10, Step 9 (line 1411). -/
theorem inner_integral_indicator_everywhere_eq {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    ∀ t ∈ Ioo 0 (2 * Real.log cutoffLambda),
    innerIntegral (1 : ℝ → ℂ) (Real.log cutoffLambda) t =
    innerIntegral (inv.B.indicator (1 : ℝ → ℂ)) (Real.log cutoffLambda) t +
    innerIntegral
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ))
      (Real.log cutoffLambda) t := by
  set L := Real.log cutoffLambda
  set I := logInterval L
  -- ae equality from Section 4
  have h_ae := inner_integral_indicator_ae_eq hLam inv
  -- Measurability of zero-extended functions
  have hφ1_meas : Measurable (zeroExtend (1 : ℝ → ℂ) I) :=
    measurable_const.indicator (measurableSet_logInterval L)
  have hφB_meas : Measurable (zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I) :=
    (measurable_const.indicator inv.B_measurable).indicator (measurableSet_logInterval L)
  have hφD_meas : Measurable (zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I) :=
    (measurable_const.indicator
      ((measurableSet_logInterval L).diff inv.B_measurable)).indicator
      (measurableSet_logInterval L)
  -- Continuity of each inner integral
  have h_cont_1 : Continuous (innerIntegral (1 : ℝ → ℂ) L) :=
    translation_norm_sq_continuous _ hφ1_meas (l2_zeroExtend_one_lt_top L)
  have h_cont_B : Continuous (innerIntegral (inv.B.indicator (1 : ℝ → ℂ)) L) :=
    translation_norm_sq_continuous _ hφB_meas
      (l2_zeroExtend_indicator_lt_top inv.B_measurable inv.B_subset)
  have h_cont_D : Continuous
      (innerIntegral ((I \ inv.B).indicator (1 : ℝ → ℂ)) L) :=
    translation_norm_sq_continuous _ hφD_meas
      (l2_zeroExtend_indicator_lt_top
        ((measurableSet_logInterval L).diff inv.B_measurable)
        diff_subset)
  -- Continuity of the sum
  have h_cont_sum : Continuous (fun t =>
      innerIntegral (inv.B.indicator (1 : ℝ → ℂ)) L t +
      innerIntegral ((I \ inv.B).indicator (1 : ℝ → ℂ)) L t) :=
    h_cont_B.add h_cont_D
  -- Apply eqOn_of_ae_eq: continuous functions agreeing a.e. on an open set
  -- agree everywhere on that set
  have h_eqOn := Measure.eqOn_of_ae_eq h_ae
    h_cont_1.continuousOn h_cont_sum.continuousOn
    (by rw [isOpen_Ioo.interior_eq]; exact subset_closure)
  exact fun t ht => h_eqOn ht

/-! ## Section 6: Soundness tests -/

-- Test 1: archEnergyIntegral_indicator_eq composes with splitting
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda) :
    archEnergyIntegral (1 : ℝ → ℂ) (Real.log cutoffLambda) =
    archEnergyIntegral (inv.B.indicator (1 : ℝ → ℂ)) (Real.log cutoffLambda) +
    archEnergyIntegral
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ))
      (Real.log cutoffLambda) :=
  archEnergyIntegral_indicator_eq hLam inv

-- Test 2: inner integral everywhere equality composes
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda)
    {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.log cutoffLambda)) :
    innerIntegral (1 : ℝ → ℂ) (Real.log cutoffLambda) t =
    innerIntegral (inv.B.indicator (1 : ℝ → ℂ)) (Real.log cutoffLambda) t +
    innerIntegral
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ))
      (Real.log cutoffLambda) t :=
  inner_integral_indicator_everywhere_eq hLam inv t ht

-- Test 3: inner integral equality composes with NormInequality
-- (inequality + equality gives both directions)
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda)
    (inv : EnergyFormSplit cutoffLambda)
    {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.log cutoffLambda)) :
    innerIntegral (1 : ℝ → ℂ) (Real.log cutoffLambda) t ≤
    innerIntegral (inv.B.indicator (1 : ℝ → ℂ)) (Real.log cutoffLambda) t +
    innerIntegral
      ((logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ))
      (Real.log cutoffLambda) t :=
  le_of_eq (inner_integral_indicator_everywhere_eq hLam inv t ht)

end

end ConnesLean
