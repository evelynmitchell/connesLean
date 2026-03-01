/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Constant Function in Form Domain — Proposition 10, Steps 1–3

Reference: lamportform.tex, Proposition 10, Steps 1–3 (lines 1312–1370).

The constant function `1` belongs to the energy form domain `D(E_λ)`,
the energy form splits when applied to `1`, and indicator complements
satisfy pointwise arithmetic identities.

## Main results

- `inner_integral_one_le`: ∫ ‖φ - S_t φ‖² ≤ 2t for φ = zeroExtend 1 I
- `archEnergyIntegral_one_lt_top`: archimedean energy of 1 is finite
- `constant_in_formDomain`: 1 ∈ D(E_λ)
- `splitting_applied_to_constant`: energy splitting applies to 1
- `indicator_complement_sum`: B and I\B indicators sum to I indicator
- `indicator_complement_disjoint`: B and I\B indicators have disjoint support
-/

import ConnesLean.Stage6.EnergyPositivity
import ConnesLean.Stage6.InvarianceSplit

/-!
# Constant Function in Form Domain

Shows that the constant function `1` is in the energy form domain,
applies the energy splitting to it, and establishes indicator complement identities.

Reference: lamportform.tex, Proposition 10, Steps 1–3 (lines 1312–1370).
-/

namespace ConnesLean

open MeasureTheory Set Real Filter ENNReal

noncomputable section

/-! ## Section 1: Inner integral bound for constant function -/

/-- For `0 < t < 2L`, the L² norm of `φ - S_t φ` is at most `2t`,
    where `φ = zeroExtend 1 I`. The function disagrees with its translate
    only on the symmetric difference `I Δ (I+t)`, which has measure `2t`. -/
theorem inner_integral_one_le {L t : ℝ} (_hL : 0 < L) (ht : 0 < t)
    (_htL : t < 2 * L) :
    ∫⁻ u, ‖zeroExtend (1 : ℝ → ℂ) (logInterval L) u -
      translationOp t (zeroExtend (1 : ℝ → ℂ) (logInterval L)) u‖₊
        ^ (2 : ℝ) ∂volume ≤ ENNReal.ofReal (2 * t) := by
  set I := logInterval L
  set φ := zeroExtend (1 : ℝ → ℂ) I
  set S := Icc (-L) (-L + t) ∪ Icc L (L + t)
  have hS_meas : MeasurableSet S := measurableSet_Icc.union measurableSet_Icc
  -- φ u = φ(u-t) outside S
  have h_eq : ∀ u, u ∉ S → φ u = φ (u - t) := by
    intro u hu
    have hu1 : u ∉ Icc (-L) (-L + t) := fun h => hu (mem_union_left _ h)
    have hu2 : u ∉ Icc L (L + t) := fun h => hu (mem_union_right _ h)
    rw [mem_Icc, not_and_or, not_le, not_le] at hu1 hu2
    by_cases hu_I : u ∈ I
    · have hut : u - t ∈ I := by
        refine mem_Ioo.mpr ⟨?_, by linarith [(mem_Ioo.mp hu_I).2]⟩
        rcases hu1 with h | h
        · exact absurd (mem_Ioo.mp hu_I).1 (not_lt.mpr h.le)
        · linarith
      simp [φ, zeroExtend_apply_mem hu_I, zeroExtend_apply_mem hut]
    · have hut : u - t ∉ I := by
        simp only [I, logInterval, mem_Ioo, not_and_or, not_lt] at hu_I ⊢
        rcases hu_I with h | h
        · left; linarith
        · rcases hu2 with h2 | h2
          · exact absurd h2 (not_lt.mpr h)
          · right; linarith
      simp [φ, zeroExtend_apply_nmem hu_I, zeroExtend_apply_nmem hut]
  -- Main bound: integrand ≤ indicator of S, then bound measure of S
  apply le_trans (lintegral_mono fun u => ?_)
  · calc ∫⁻ u, S.indicator (fun _ => (1 : ENNReal)) u ∂volume
        = volume S := lintegral_indicator_one hS_meas
      _ ≤ volume (Icc (-L) (-L + t)) + volume (Icc L (L + t)) :=
          measure_union_le _ _
      _ = ENNReal.ofReal t + ENNReal.ofReal t := by
          congr 1 <;> rw [Real.volume_Icc] <;> ring_nf
      _ = ENNReal.ofReal (2 * t) := by
          rw [← ENNReal.ofReal_add (le_of_lt ht) (le_of_lt ht)]; ring_nf
  · -- Pointwise: integrand ≤ indicator S
    simp only [translationOp_apply]
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      by_cases h1 : u ∈ I <;> by_cases h2 : (u - t) ∈ I <;>
        simp [φ, zeroExtend_apply_mem, zeroExtend_apply_nmem, h1, h2]
    · rw [Set.indicator_of_notMem hu, h_eq u hu]; simp

/-! ## Section 2: Archimedean energy finiteness -/

/-- The archimedean energy integral of the constant function is finite.
    Combines `archWeight(t) ≤ exp(t/2)/(2t)` with inner integral `≤ 2t`
    to get integrand `≤ exp(L)`, then integrates over `(0, 2L)`. -/
theorem archEnergyIntegral_one_lt_top {L : ℝ} (hL : 0 < L) :
    archEnergyIntegral (1 : ℝ → ℂ) L < ⊤ := by
  unfold archEnergyIntegral
  calc ∫⁻ t in Ioo 0 (2 * L), archEnergyIntegrand (1 : ℝ → ℂ) L t
      ≤ ∫⁻ _t in Ioo 0 (2 * L), ENNReal.ofReal (Real.exp L) := by
        apply setLIntegral_mono_ae measurable_const.aemeasurable
        filter_upwards with t ht
        -- Pointwise bound: archEnergyIntegrand 1 L t ≤ exp(L)
        unfold archEnergyIntegrand
        have ht_pos : 0 < t := ht.1
        have htL : t < 2 * L := ht.2
        calc ↑(archWeight t).toNNReal * ∫⁻ u,
              ‖zeroExtend (1 : ℝ → ℂ) (logInterval L) u -
                translationOp t (zeroExtend (1 : ℝ → ℂ) (logInterval L)) u‖₊
                  ^ (2 : ℝ) ∂volume
            ≤ ENNReal.ofReal (Real.exp (t / 2) / (2 * t)) *
                ENNReal.ofReal (2 * t) := by
              apply mul_le_mul'
              · exact ENNReal.ofReal_le_ofReal (archWeight_le_inv_two_t ht_pos)
              · exact inner_integral_one_le hL ht_pos htL
          _ = ENNReal.ofReal (Real.exp (t / 2)) := by
              rw [← ENNReal.ofReal_mul
                (le_of_lt (div_pos (Real.exp_pos _) (by linarith)))]
              congr 1; field_simp
          _ ≤ ENNReal.ofReal (Real.exp L) := by
              apply ENNReal.ofReal_le_ofReal
              exact Real.exp_le_exp_of_le (by linarith)
    _ = ENNReal.ofReal (Real.exp L) * volume (Ioo 0 (2 * L)) :=
        setLIntegral_const _ _
    _ < ⊤ := by
        apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top

/-! ## Section 3: Constant function in form domain -/

/-- The inner integral of the constant function is finite for any shift.
    The integrand ≤ 1 on `I ∪ (I + shift)`, both of which have measure `2L`. -/
theorem inner_integral_one_lt_top (L shift : ℝ) :
    ∫⁻ u, ‖zeroExtend (1 : ℝ → ℂ) (logInterval L) u -
      translationOp shift (zeroExtend (1 : ℝ → ℂ) (logInterval L)) u‖₊
        ^ (2 : ℝ) ∂volume < ⊤ := by
  set I := logInterval L
  set J := (· - shift) ⁻¹' I
  have hJ_meas : MeasurableSet J :=
    (measurableSet_logInterval L).preimage (measurable_id.sub measurable_const)
  calc ∫⁻ u, ‖zeroExtend (1 : ℝ → ℂ) I u -
          translationOp shift (zeroExtend (1 : ℝ → ℂ) I) u‖₊
            ^ (2 : ℝ) ∂volume
      ≤ ∫⁻ u, I.indicator (fun _ => (1 : ENNReal)) u +
          J.indicator (fun _ => (1 : ENNReal)) u ∂volume := by
        apply lintegral_mono; intro u; simp only [translationOp_apply]
        by_cases h1 : u ∈ I <;> by_cases h2 : (u - shift) ∈ I <;>
          simp [zeroExtend_apply_mem, zeroExtend_apply_nmem, h1, h2,
                Set.indicator_of_mem, Set.indicator_of_notMem, J, mem_preimage]
    _ = volume I + volume J := by
        rw [lintegral_add_right _ (measurable_const.indicator hJ_meas)]
        congr 1
        · exact lintegral_indicator_one (measurableSet_logInterval L)
        · exact lintegral_indicator_one hJ_meas
    _ = volume I + volume I := by
        rw [(measurePreserving_sub_const shift).measure_preimage
          (measurableSet_logInterval L).nullMeasurableSet]
    _ < ⊤ := by
        apply ENNReal.add_lt_top.mpr ⟨?_, ?_⟩ <;>
        · rw [show I = Ioo (-L) L from rfl, Real.volume_Ioo]; exact ofReal_lt_top

/-- The constant function `1` belongs to the form domain `D(E_λ)`:
    its energy form is finite. The archimedean part is finite by
    `archEnergyIntegral_one_lt_top`, and the prime part is a finite
    sum of finite terms. -/
theorem constant_in_formDomain {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    (1 : ℝ → ℂ) ∈ formDomain cutoffLambda := by
  unfold formDomain energyForm
  set L := Real.log cutoffLambda
  have hL : 0 < L := Real.log_pos hLam
  apply ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · exact ne_top_of_lt (archEnergyIntegral_one_lt_top hL)
  · apply ne_top_of_lt
    apply ENNReal.sum_lt_top.mpr; intro p _hp
    show totalPrimeEnergy p cutoffLambda 1 L < ⊤
    unfold totalPrimeEnergy
    apply ENNReal.sum_lt_top.mpr; intro m _hm
    show primeEnergyTerm p m 1 L < ⊤
    unfold primeEnergyTerm
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      (inner_integral_one_lt_top L _)

/-! ## Section 4: Splitting applied to constant -/

/-- The energy of the constant function splits across any `EnergyFormSplit`.
    Direct application of `EnergyFormSplit.split` with `G = 1`. -/
theorem splitting_applied_to_constant {cutoffLambda : ℝ}
    (hLam : 1 < cutoffLambda) (inv : EnergyFormSplit cutoffLambda) :
    inv.B.indicator (1 : ℝ → ℂ) ∈ formDomain cutoffLambda ∧
    (logInterval (Real.log cutoffLambda) \ inv.B).indicator (1 : ℝ → ℂ) ∈
      formDomain cutoffLambda ∧
    energyForm cutoffLambda (1 : ℝ → ℂ) =
      energyForm cutoffLambda (inv.B.indicator 1) +
      energyForm cutoffLambda
        ((logInterval (Real.log cutoffLambda) \ inv.B).indicator 1) :=
  inv.split 1 (constant_in_formDomain hLam)

/-! ## Section 5: Indicator complement arithmetic -/

/-- For `B ⊆ I`, the zero-extended indicators of `B` and `I \ B` sum to
    the zero-extended constant function: `1_B + 1_{I\B} = 1_I` pointwise.

    Uses `Set.indicator_indicator` to simplify `I.indicator (B.indicator f)
    = (I ∩ B).indicator f`, which reduces to `B.indicator f` when `B ⊆ I`. -/
theorem indicator_complement_sum {B I : Set ℝ} (hB : B ⊆ I) (u : ℝ) :
    zeroExtend (B.indicator (1 : ℝ → ℂ)) I u +
      zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I u =
    zeroExtend (1 : ℝ → ℂ) I u := by
  simp only [zeroExtend_eq_indicator]
  rw [Set.indicator_indicator, Set.inter_eq_right.mpr hB,
      Set.indicator_indicator,
      show I ∩ (I \ B) = I \ B by ext x; simp [mem_inter_iff, mem_diff]]
  by_cases hu_B : u ∈ B
  · simp [Set.indicator_of_mem hu_B,
          Set.indicator_of_notMem (fun h : u ∈ I \ B => h.2 hu_B),
          Set.indicator_of_mem (hB hu_B)]
  · by_cases hu_I : u ∈ I
    · simp [Set.indicator_of_notMem hu_B,
            Set.indicator_of_mem (show u ∈ I \ B from ⟨hu_I, hu_B⟩),
            Set.indicator_of_mem hu_I]
    · simp [Set.indicator_of_notMem hu_B,
            Set.indicator_of_notMem (fun h : u ∈ I \ B => hu_I h.1),
            Set.indicator_of_notMem hu_I]

/-- For any `B`, the zero-extended indicators of `B` and `I \ B` have
    disjoint support: their product is zero at every point.

    Since `B` and `I \ B` are disjoint, at most one indicator is nonzero
    at any point, making their product zero. -/
theorem indicator_complement_disjoint {B I : Set ℝ} (hB : B ⊆ I) (u : ℝ) :
    zeroExtend (B.indicator (1 : ℝ → ℂ)) I u *
      zeroExtend ((I \ B).indicator (1 : ℝ → ℂ)) I u = 0 := by
  simp only [zeroExtend_eq_indicator]
  rw [Set.indicator_indicator, Set.inter_eq_right.mpr hB,
      Set.indicator_indicator,
      show I ∩ (I \ B) = I \ B by ext x; simp [mem_inter_iff, mem_diff]]
  by_cases hu_B : u ∈ B
  · simp [Set.indicator_of_mem hu_B,
          Set.indicator_of_notMem (fun h : u ∈ I \ B => h.2 hu_B)]
  · simp [Set.indicator_of_notMem hu_B]

/-! ## Section 6: Soundness tests -/

-- Test 1: splitting_applied_to_constant composes with indicator_complement_sum
example {cutoffLambda : ℝ}
    (inv : EnergyFormSplit cutoffLambda) (u : ℝ) :
    let I := logInterval (Real.log cutoffLambda)
    zeroExtend (inv.B.indicator (1 : ℝ → ℂ)) I u +
      zeroExtend ((I \ inv.B).indicator (1 : ℝ → ℂ)) I u =
    zeroExtend (1 : ℝ → ℂ) I u :=
  indicator_complement_sum inv.B_subset u

-- Test 2: constant_in_formDomain produces a formDomain membership proof
example {cutoffLambda : ℝ} (hLam : 1 < cutoffLambda) :
    energyForm cutoffLambda (1 : ℝ → ℂ) ≠ ⊤ :=
  constant_in_formDomain hLam

-- Test 3: indicator_complement_disjoint at the boundary (B = ∅)
example (I : Set ℝ) (u : ℝ) :
    zeroExtend ((∅ : Set ℝ).indicator (1 : ℝ → ℂ)) I u *
      zeroExtend ((I \ ∅).indicator (1 : ℝ → ℂ)) I u = 0 :=
  indicator_complement_disjoint (Set.empty_subset I) u

-- Test 4: complement sum with B = ∅ gives full indicator
example (I : Set ℝ) (u : ℝ) :
    zeroExtend ((∅ : Set ℝ).indicator (1 : ℝ → ℂ)) I u +
      zeroExtend ((I \ ∅).indicator (1 : ℝ → ℂ)) I u =
    zeroExtend (1 : ℝ → ℂ) I u :=
  indicator_complement_sum (Set.empty_subset I) u

end

end ConnesLean
