/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mollification and Constancy of Translation-Invariant Indicators

Reference: lamportform.tex, Section 6, Lemma 6, Steps 4–5 (lines 577–599).

This file proves that if an indicator `1_B` is ae translation-invariant on an
open interval `I`, then its local (rectangular) average is constant on compact
subintervals of `I`.

The key steps:
1. Forward shift: convert `f(u) = f(u-t)` ae to `f(x+t) = f(x)` ae (using
   translation invariance of Lebesgue measure).
2. Local average shift: under ae shift-invariance, `localAverage f η (u+t) =
   localAverage f η u` (change of variables + ae congruence).
3. Constancy via telescoping: iterate small shifts to cover any compact
   subinterval, using `Nat.floor` for step counting.
4. Connection: combine with `IndicatorTranslationInvariant` to get constancy
   of the indicator's local average.
-/

import ConnesLean.Stage4.TranslationInvariance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace ConnesLean

open MeasureTheory Set Filter Metric intervalIntegral

noncomputable section

/-! ## Local average (rectangular mollifier) -/

/-- The local average of `f` with radius `η` at point `u`:
    `(2η)⁻¹ ∫_{u-η}^{u+η} f(s) ds`.

    This is the simplest rectangular mollifier. When `f = 1_B`, this
    gives the density of `B` in the interval `[u-η, u+η]`.

    Reference: lamportform.tex, Lemma 6, Step 4. -/
def localAverage (f : ℝ → ℝ) (η : ℝ) (u : ℝ) : ℝ :=
  (2 * η)⁻¹ * ∫ s in (u - η)..(u + η), f s

theorem localAverage_apply (f : ℝ → ℝ) (η u : ℝ) :
    localAverage f η u = (2 * η)⁻¹ * ∫ s in (u - η)..(u + η), f s := rfl

/-! ## Forward shift of ae properties -/

/-- Forward shift: if `f(u) = f(u-t)` ae on `Icc a b`, then `f(x+t) = f(x)` ae
    for `x ∈ Icc (a-t) (b-t)`.

    Uses translation invariance of Lebesgue measure (`measure_preimage_add_right`):
    null sets are preserved under shifts, so ae properties transfer. -/
theorem ae_indicator_forward_shift {f : ℝ → ℝ} {a b t : ℝ}
    (h : ∀ᵐ u ∂(volume.restrict (Icc a b)), f u = f (u - t)) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Icc (a - t) (b - t) → f (x + t) = f x := by
  rw [ae_restrict_iff' measurableSet_Icc] at h
  rw [Filter.Eventually] at h ⊢
  apply Filter.mem_of_superset (x := (· + t) ⁻¹' {u | u ∈ Icc a b → f u = f (u - t)})
  · rw [mem_ae_iff, ← Set.preimage_compl, measure_preimage_add_right]
    exact mem_ae_iff.mp h
  · intro x (hx : (x + t) ∈ Icc a b → f (x + t) = f ((x + t) - t)) hx_mem
    have hxt_mem : x + t ∈ Icc a b := ⟨by linarith [hx_mem.1], by linarith [hx_mem.2]⟩
    have := hx hxt_mem
    rwa [add_sub_cancel_right] at this

/-! ## Translation invariance of local average -/

/-- The local average is shift-invariant when the underlying function is ae
    shift-invariant.

    If `f(u) = f(u-t)` ae on `Icc a b`, and `[u-η, u+η+t] ⊆ [a, b]`, then
    `localAverage f η (u+t) = localAverage f η u`.

    Proof: change of variables `s ↦ s+t` maps the shifted integration interval
    back to the original, then `integral_congr_ae` applies the ae hypothesis.

    Reference: lamportform.tex, Lemma 6, Step 4. -/
theorem localAverage_shift_eq {f : ℝ → ℝ} {a b t η u : ℝ}
    (hη : 0 < η) (ht : 0 < t)
    (h_ae : ∀ᵐ u ∂(volume.restrict (Icc a b)), f u = f (u - t))
    (h_contain : Icc (u - η) (u + η + t) ⊆ Icc a b) :
    localAverage f η (u + t) = localAverage f η u := by
  unfold localAverage
  congr 1
  conv_lhs =>
    rw [show u + t - η = u - η + t from by ring, show u + t + η = u + η + t from by ring]
  rw [← integral_comp_add_right f t]
  apply intervalIntegral.integral_congr_ae
  have h_fwd := ae_indicator_forward_shift h_ae
  filter_upwards [h_fwd] with s hs hs_mem
  apply hs
  rw [Set.uIoc_of_le (by linarith : u - η ≤ u + η)] at hs_mem
  have h_lo : a ≤ u - η := (h_contain (left_mem_Icc.mpr (by linarith))).1
  have h_hi : u + η + t ≤ b := (h_contain (right_mem_Icc.mpr (by linarith))).2
  exact ⟨by linarith [hs_mem.1], by linarith [hs_mem.2]⟩

/-! ## Constancy via telescoping -/

/-- Helper: shifting by `n` equal steps of size `δ/2` preserves the local average.
    By induction on `n`: each step applies `h_shift` with `t = δ/2 < δ`. -/
private theorem localAverage_shift_n {f : ℝ → ℝ} {a b η δ : ℝ}
    (hδ : 0 < δ)
    (h_shift : ∀ u t, a ≤ u - η → u + η + t ≤ b → 0 < t → t < δ →
      localAverage f η (u + t) = localAverage f η u)
    (n : ℕ) (c : ℝ) (hc : a + η ≤ c) (hn : c + ↑n * (δ / 2) + η ≤ b) :
    localAverage f η (c + ↑n * (δ / 2)) = localAverage f η c := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk_bound : c + ↑k * (δ / 2) + η ≤ b := by
      calc c + ↑k * (δ / 2) + η
          ≤ c + ↑(k + 1) * (δ / 2) + η := by push_cast; nlinarith
        _ ≤ b := hn
    rw [show c + ↑(k + 1) * (δ / 2) = (c + ↑k * (δ / 2)) + δ / 2 from by push_cast; ring]
    rw [h_shift (c + ↑k * (δ / 2)) (δ / 2)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
      (by push_cast at hn ⊢; nlinarith)
      (by linarith) (by linarith)]
    exact ih hk_bound

/-- The local average is constant on `[a+η, b-η]` when the underlying function
    is ae shift-invariant for all small shifts.

    This is the telescoping argument: any point `v ∈ [a+η, b-η]` can be
    connected to `a+η` by a chain of small shifts, each preserving the local
    average. Uses `Nat.floor` to compute the number of intermediate steps.

    Reference: lamportform.tex, Lemma 6, Step 5 (constancy of mollified function). -/
theorem localAverage_const_on_compact {f : ℝ → ℝ} {a b η δ : ℝ}
    (hδ : 0 < δ)
    (h_shift : ∀ u t, a ≤ u - η → u + η + t ≤ b → 0 < t → t < δ →
      localAverage f η (u + t) = localAverage f η u) :
    ∀ v, a + η ≤ v → v ≤ b - η → localAverage f η v = localAverage f η (a + η) := by
  intro v hv_lo hv_hi
  by_cases heq : v = a + η
  · rw [heq]
  have hv_lt : a + η < v := lt_of_le_of_ne hv_lo (Ne.symm heq)
  set c := a + η
  set gap := v - c with hgap_def
  have hgap_pos : 0 < gap := by linarith
  set step := δ / 2 with hstep_def
  have hstep_pos : 0 < step := by linarith
  set n := ⌊gap / step⌋₊
  have h_floor_le : ↑n * step ≤ gap :=
    (le_div_iff₀ hstep_pos).mp
      (Nat.floor_le (div_nonneg (le_of_lt hgap_pos) (le_of_lt hstep_pos)))
  have h_floor_lt : gap < (↑n + 1) * step :=
    (div_lt_iff₀ hstep_pos).mp (Nat.lt_floor_add_one (gap / step))
  have hn_bound : c + ↑n * step + η ≤ b := by
    have : c + ↑n * step ≤ v := by linarith
    linarith
  have h_n_eq := localAverage_shift_n hδ h_shift n c (le_refl c) hn_bound
  by_cases hresid_zero : v = c + ↑n * step
  · rw [hresid_zero, h_n_eq]
  · have hresid_pos : 0 < v - (c + ↑n * step) :=
      lt_of_le_of_ne (by linarith) (Ne.symm (sub_ne_zero.mpr hresid_zero))
    have h_last := h_shift (c + ↑n * step) (v - (c + ↑n * step))
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      (by linarith)
      hresid_pos
      (by linarith)
    rw [show (c + ↑n * step) + (v - (c + ↑n * step)) = v from by ring] at h_last
    rw [h_last, h_n_eq]

/-! ## Connection to IndicatorTranslationInvariant -/

/-- The local average of `1_B` is constant on compact subintervals when `1_B`
    is ae translation-invariant on an open interval.

    Combines:
    - `indicator_ae_shift_forall_small` (from TranslationInvariance.lean): ae
      shift-invariance on `Icc a b` for all small `t`.
    - `localAverage_shift_eq`: each small shift preserves the local average.
    - `localAverage_const_on_compact`: telescoping gives constancy.

    Reference: lamportform.tex, Lemma 6, conclusion of Step 5. -/
theorem localAverage_const_of_indicator_invariant
    {B I : Set ℝ} {ε : ℝ} (h : IndicatorTranslationInvariant B I ε)
    {α β a b : ℝ} (hI : I = Ioo α β) (hαa : α < a) (hbβ : b < β)
    {η : ℝ} (hη : 0 < η) :
    ∀ v, a + η ≤ v → v ≤ b - η →
      localAverage (B.indicator (1 : ℝ → ℝ)) η v =
      localAverage (B.indicator (1 : ℝ → ℝ)) η (a + η) := by
  obtain ⟨hδ_pos, h_ae_shift⟩ := indicator_ae_shift_forall_small h hI hαa hbβ
  apply localAverage_const_on_compact hδ_pos
  intro u t hu_lo hu_hi ht_pos ht_δ
  exact localAverage_shift_eq hη ht_pos (h_ae_shift t ht_pos ht_δ)
    (Icc_subset_Icc (by linarith) (by linarith))

/-! ## Lebesgue differentiation -/

/-- The local average equals the closed-ball average for Lebesgue measure on `ℝ`.
    This is the bridge between our `localAverage` definition and Mathlib's
    `setAverage` over `closedBall`. -/
theorem closedBall_average_eq_localAverage (f : ℝ → ℝ) (x r : ℝ) (hr : 0 < r) :
    ⨍ y in closedBall x r, f y ∂volume = localAverage f r x := by
  unfold localAverage
  rw [setAverage_eq, Real.closedBall_eq_Icc]
  simp only [smul_eq_mul, mul_inv_rev]
  rw [intervalIntegral_eq_integral_uIoc]
  simp only [show x - r ≤ x + r by linarith,
    uIoc_of_le (show x - r ≤ x + r by linarith), if_true, one_smul]
  rw [integral_Icc_eq_integral_Ioc]
  have hv : (volume.real (Icc (x - r) (x + r))) = 2 * r := by
    rw [Measure.real, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ (x + r) - (x - r))]
    ring
  rw [hv]; ring

set_option maxHeartbeats 400000 in
-- IsUnifLocDoublingMeasure instance search is expensive
/-- **Lebesgue differentiation**: `localAverage f η x → f x` ae as `η → 0⁺`.

    For any locally integrable `f`, the rectangular average over `[x-η, x+η]`
    converges to `f(x)` at almost every `x` as the radius `η → 0⁺`.

    Proof: connect `localAverage` to the closed-ball average via
    `closedBall_average_eq_localAverage`, then apply Mathlib's
    `IsUnifLocDoublingMeasure.ae_tendsto_average` with centered balls.

    Reference: lamportform.tex, Lemma 6, Step 5 (convergence of mollifier). -/
theorem localAverage_tendsto_ae (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun η => localAverage f η x) (nhdsWithin 0 (Ioi 0)) (nhds (f x)) := by
  have h := IsUnifLocDoublingMeasure.ae_tendsto_average
    (μ := (volume : Measure ℝ)) hf 1
  filter_upwards [h] with x hx
  have hmem : ∀ᶠ η in nhdsWithin (0 : ℝ) (Ioi 0), x ∈ closedBall x (1 * η) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    simp [mem_closedBall]; linarith [mem_Ioi.mp hη]
  have h1 := hx (fun _ => x) id tendsto_id hmem
  change Tendsto (fun η => localAverage f η x)
    (nhdsWithin 0 (Ioi 0)) (nhds (f x))
  apply Tendsto.congr' _ h1
  filter_upwards [self_mem_nhdsWithin] with η hη
  simp only [id]
  exact closedBall_average_eq_localAverage f x η (mem_Ioi.mp hη)

end

end ConnesLean
