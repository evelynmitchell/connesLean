/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Constant in Form Domain — Proposition 10, Steps 1–3

Reference: lamportform.tex, Proposition 10 (lines 1312–1370).

Proves that the constant function 1 belongs to the form domain D(E_λ),
applies the energy splitting from 6B, and establishes the indicator
complement decomposition f + g = 1̃, f·g = 0.

This is the middle step of the irreducibility chain (6A → 6B → **6C** → 6D → 6E).

## Main results

- `constant_in_formDomain`: E_λ(1) < ∞, so 1 ∈ D(E_λ)
- `splitting_applied_to_constant`: E_λ(1) = E_λ(1_B) + E_λ(1_{I\B})
- `indicator_complement_sum`: f + g = 1̃ (pointwise)
- `indicator_complement_mul_zero`: f·g = 0 (pointwise)
-/

import ConnesLean.Stage6.IndicatorEnergy
import ConnesLean.Stage6.InvarianceSplit

namespace ConnesLean

open MeasureTheory Real Finset Set ENNReal

noncomputable section

/-! ## Helpers for finiteness of energy on constant functions -/

/-- Pointwise: the ‖1_A(u) − 1_B(u)‖₊² integrand equals the symmDiff indicator.
    Used to bridge L² norms of indicator differences to symmetric difference measure. -/
private theorem indicator_nnnorm_sq_eq_symmDiff_indicator
    {A B : Set ℝ} (u : ℝ)
    (hA_mem : Decidable (u ∈ A)) (hB_mem : Decidable (u ∈ B)) :
    (‖A.indicator (fun _ => (1 : ℂ)) u -
      B.indicator (fun _ => (1 : ℂ)) u‖₊ : ENNReal) ^ (2 : ℝ) =
    (symmDiff A B).indicator (1 : ℝ → ENNReal) u := by
  by_cases hAu : u ∈ A <;> by_cases hBu : u ∈ B
  · simp only [Set.indicator_of_mem hAu, Set.indicator_of_mem hBu,
      sub_self, nnnorm_zero, ENNReal.coe_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [Set.indicator_of_notMem (by simp [Set.mem_symmDiff, hAu, hBu])]
  · simp only [Set.indicator_of_mem hAu, Set.indicator_of_notMem hBu,
      sub_zero, nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow]
    rw [Set.indicator_of_mem
      (Set.mem_symmDiff.mpr (Or.inl ⟨hAu, hBu⟩))]; simp
  · simp only [Set.indicator_of_notMem hAu, Set.indicator_of_mem hBu,
      zero_sub, nnnorm_neg, nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow]
    rw [Set.indicator_of_mem
      (Set.mem_symmDiff.mpr (Or.inr ⟨hBu, hAu⟩))]; simp
  · simp only [Set.indicator_of_notMem hAu, Set.indicator_of_notMem hBu,
      sub_self, nnnorm_zero, ENNReal.coe_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [Set.indicator_of_notMem (by simp [Set.mem_symmDiff, hAu, hBu])]

/-- Bridge between L² distance of indicator functions and symmetric difference
    measure. For indicators of {0,1}-valued constant functions,
    ∫ ‖1_A − 1_B‖² = μ(A △ B). -/
private theorem lintegral_norm_sq_indicator_diff_eq_symmDiff
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ u, ‖A.indicator (fun _ => (1 : ℂ)) u -
           B.indicator (fun _ => (1 : ℂ)) u‖₊ ^ (2 : ℝ) ∂volume =
    volume (symmDiff A B) := by
  rw [lintegral_congr (fun u => indicator_nnnorm_sq_eq_symmDiff_indicator u
    (Classical.dec _) (Classical.dec _)),
    lintegral_indicator_one (hA.symmDiff hB)]

/-- Shifted interval identity: preimage of Ioo(-L,L) under (· − s)
    is Ioo(-L+s, L+s). -/
private theorem preimage_sub_logInterval (L s : ℝ) :
    Set.preimage (· - s) (logInterval L) = Set.Ioo (-L + s) (L + s) := by
  ext u; simp [logInterval, Set.mem_Ioo]

/-- Weight bound: archWeight(t) · (2t) ≤ exp(t/2) for t > 0. -/
private theorem archWeight_mul_le_exp {t : ℝ} (ht : 0 < t) :
    archWeight t * (2 * t) ≤ Real.exp (t / 2) := by
  unfold archWeight
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * Real.sinh t)]
  calc Real.exp (t / 2) * (2 * t)
      = 2 * t * Real.exp (t / 2) := by ring
    _ ≤ 2 * Real.sinh t * Real.exp (t / 2) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (sinh_ge_self (le_of_lt ht))
            (by norm_num)
        · exact le_of_lt (Real.exp_pos _)
    _ = Real.exp (t / 2) * (2 * Real.sinh t) := by ring

/-- Measurability of the preimage set (· − t) ⁻¹' logInterval L. -/
private theorem measurableSet_preimage_sub_logInterval (L t : ℝ) :
    MeasurableSet ((· - t) ⁻¹' logInterval L : Set ℝ) :=
  (measurableSet_logInterval L).preimage (measurable_id.sub measurable_const)

/-- Rewrite translationOp of a zero-extended constant indicator to a preimage
    indicator. For constant functions, translationOp t (I.indicator 1) u =
    ((· − t) ⁻¹' I).indicator 1 u. -/
private theorem translationOp_zeroExtend_constant_eq_preimage_indicator
    (L t : ℝ) (u : ℝ) :
    translationOp t (zeroExtend (fun _ => (1 : ℂ)) (logInterval L)) u =
    ((· - t) ⁻¹' logInterval L).indicator (fun _ => (1 : ℂ)) u := by
  unfold translationOp zeroExtend
  by_cases h : u - t ∈ logInterval L
  · simp [Set.indicator_of_mem h,
          Set.indicator_of_mem (show u ∈ (· - t) ⁻¹' logInterval L from h)]
  · simp [Set.indicator_of_notMem h,
          Set.indicator_of_notMem
            (show u ∉ (· - t) ⁻¹' logInterval L from h)]

/-- The inner L² integral for the constant function 1 equals the symmetric
    difference measure. -/
private theorem inner_integral_constant_eq_symmDiff (L t : ℝ) :
    ∫⁻ u, ‖(logInterval L).indicator (fun _ => (1 : ℂ)) u -
      ((· - t) ⁻¹' logInterval L).indicator
        (fun _ => (1 : ℂ)) u‖₊ ^ (2 : ℝ) ∂volume =
    volume (symmDiff (logInterval L) ((· - t) ⁻¹' logInterval L)) :=
  lintegral_norm_sq_indicator_diff_eq_symmDiff
    (measurableSet_logInterval L) (measurableSet_preimage_sub_logInterval L t)

/-- Pointwise bound on archimedean integrand for the constant function 1. -/
private theorem archEnergyIntegrand_constant_le {L : ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 (2 * L)) :
    archEnergyIntegrand (fun _ => (1 : ℂ)) L t ≤
      ENNReal.ofReal (Real.exp L) := by
  have ht_pos : 0 < t := ht.1
  have ht_2L : t < 2 * L := ht.2
  unfold archEnergyIntegrand
  simp_rw [translationOp_zeroExtend_constant_eq_preimage_indicator L t, zeroExtend]
  rw [inner_integral_constant_eq_symmDiff,
      symm_diff_logInterval_measure ht_pos ht_2L]
  -- ↑(archWeight t).toNNReal = ofReal(archWeight t) by definitional unfolding
  change ENNReal.ofReal (archWeight t) * ENNReal.ofReal (2 * t) ≤
    ENNReal.ofReal (Real.exp L)
  rw [← ENNReal.ofReal_mul (le_of_lt (archWeight_pos ht_pos))]
  exact ENNReal.ofReal_le_ofReal (le_trans (archWeight_mul_le_exp ht_pos)
    (Real.exp_le_exp.mpr (by linarith)))

/-- Each prime energy term for the constant function 1 is finite. -/
private theorem primeEnergyTerm_constant_lt_top (p m : ℕ) (L : ℝ) :
    primeEnergyTerm p m (fun _ => (1 : ℂ)) L < ⊤ := by
  unfold primeEnergyTerm
  apply ENNReal.mul_lt_top ENNReal.coe_lt_top
  simp_rw [translationOp_zeroExtend_constant_eq_preimage_indicator, zeroExtend]
  rw [inner_integral_constant_eq_symmDiff]
  calc volume (symmDiff (logInterval L)
        ((· - ↑m * Real.log ↑p) ⁻¹' logInterval L))
      ≤ volume (logInterval L ∪
        ((· - ↑m * Real.log ↑p) ⁻¹' logInterval L)) :=
        measure_mono symmDiff_subset_union
    _ ≤ volume (logInterval L) + volume
        ((· - ↑m * Real.log ↑p) ⁻¹' logInterval L) :=
        measure_union_le _ _
    _ < ⊤ := by
        rw [preimage_sub_logInterval]
        exact ENNReal.add_lt_top.mpr ⟨measure_Ioo_lt_top, measure_Ioo_lt_top⟩

/-! ## Main theorem: constant function in form domain -/

/-- **Proposition 10, Step 1**: The constant function 1 belongs to D(E_λ),
    i.e., E_λ(1) < ∞.

    The archimedean integrand is bounded by exp(L) (a constant), and the
    integration domain Ioo(0, 2L) has finite measure, giving a finite
    archimedean contribution. Each prime term is finite by the
    L²-symmetric difference bound.

    Reference: lamportform.tex, Prop 10, Step 1, lines 1320–1340. -/
theorem constant_in_formDomain (cutoffLambda : ℝ) :
    (fun _ => (1 : ℂ)) ∈ formDomain cutoffLambda := by
  change energyForm cutoffLambda (fun _ => 1) ≠ ⊤
  unfold energyForm
  set L := Real.log cutoffLambda
  -- Archimedean part is finite
  have h_arch : archEnergyIntegral (fun _ => (1 : ℂ)) L < ⊤ := by
    unfold archEnergyIntegral
    calc ∫⁻ t in Set.Ioo 0 (2 * L),
          archEnergyIntegrand (fun _ => (1 : ℂ)) L t ∂volume
        ≤ ∫⁻ _ in Set.Ioo 0 (2 * L),
          ENNReal.ofReal (Real.exp L) ∂volume :=
          setLIntegral_mono measurable_const
            (fun t ht => archEnergyIntegrand_constant_le ht)
      _ = ENNReal.ofReal (Real.exp L) * volume (Set.Ioo 0 (2 * L)) :=
          setLIntegral_const _ _
      _ < ⊤ :=
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top
  -- Prime sum is finite
  have h_prime : ∑ p ∈ primeFinset cutoffLambda,
      totalPrimeEnergy p cutoffLambda (fun _ => (1 : ℂ)) L < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro p _
    unfold totalPrimeEnergy
    apply ENNReal.sum_lt_top.mpr
    intro m _
    exact primeEnergyTerm_constant_lt_top p m L
  exact (ENNReal.add_lt_top.mpr ⟨h_arch, h_prime⟩).ne

/-! ## Applying the splitting to the constant function -/

/-- **Proposition 10, Step 2**: Applying `invariance_split` to G = 1.
    The energy of the constant function decomposes as
    E_λ(1) = E_λ(1_B) + E_λ(1_{I\B}).

    Reference: lamportform.tex, Prop 10, Step 2, lines 1342–1350. -/
theorem splitting_applied_to_constant (cutoffLambda : ℝ)
    (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) :
    energyForm cutoffLambda (fun _ => (1 : ℂ)) =
      energyForm cutoffLambda
        (ideal.B.indicator (fun _ => (1 : ℂ))) +
      energyForm cutoffLambda
        ((logInterval (Real.log cutoffLambda) \ ideal.B).indicator
          (fun _ => (1 : ℂ))) :=
  invariance_split cutoffLambda hLam ideal _
    (constant_in_formDomain cutoffLambda)

/-! ## Indicator complement decomposition -/

/-- **Proposition 10, Step 3a**: f + g = 1̃ pointwise, where
    f = zeroExtend(1_B) and g = zeroExtend(1_{I\B}).

    Reference: lamportform.tex, Prop 10, Step 3, lines 1352–1360. -/
theorem indicator_complement_sum {B : Set ℝ} {L : ℝ} :
    (fun u =>
      zeroExtend (B.indicator (fun _ => (1 : ℂ))) (logInterval L) u +
      zeroExtend ((logInterval L \ B).indicator (fun _ => (1 : ℂ)))
        (logInterval L) u) =
    zeroExtend (fun _ => (1 : ℂ)) (logInterval L) := by
  funext u; unfold zeroExtend
  by_cases hI : u ∈ logInterval L <;> by_cases hB : u ∈ B <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, *]

/-- **Proposition 10, Step 3b**: f · g = 0 pointwise. The indicator
    projections onto B and I \ B have disjoint supports.

    Reference: lamportform.tex, Prop 10, Step 3, lines 1362–1370. -/
theorem indicator_complement_mul_zero {B : Set ℝ} {L : ℝ} :
    (fun u =>
      zeroExtend (B.indicator (fun _ => (1 : ℂ))) (logInterval L) u *
      zeroExtend ((logInterval L \ B).indicator (fun _ => (1 : ℂ)))
        (logInterval L) u) =
    (0 : ℝ → ℂ) := by
  funext u; unfold zeroExtend
  by_cases hI : u ∈ logInterval L <;> by_cases hB : u ∈ B <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, *]

end

end ConnesLean
