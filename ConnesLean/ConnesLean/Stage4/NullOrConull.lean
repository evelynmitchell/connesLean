/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Null or Conull Conclusion for Translation-Invariant Indicators

Reference: lamportform.tex, Section 6, Lemma 6, Steps 8–10 (lines 617–639).

This file completes Lemma 6: from the constant mollifier values on nested
compact subsets (proved in `MollificationConstancy.lean`), we conclude that
a translation-invariant indicator on an open interval is either ae-null or
ae-conull.

The key steps:
1. **Compact case** (`indicator_null_or_conull_on_compact`): On any compact
   `[c, d] ⊂ (α, β)`, by Lebesgue differentiation + limit uniqueness, either
   `volume (B ∩ [c, d]) = 0` or `volume ([c, d] \ B) = 0`.
2. **Exhaustion**: The open interval `(α, β)` is covered by increasing compact
   subintervals `K_n`. The null/conull alternative is consistent across all K_n
   (by the anchor-interval argument), so the global conclusion follows.
-/

import ConnesLean.Stage4.MollificationConstancy

/-!
# Null or Conull Conclusion — Lemma 6

Completes Lemma 6: a translation-invariant indicator on an open interval is either
ae-null or ae-conull. Uses Lebesgue differentiation on compact subsets to establish
the dichotomy, then exhaustion by increasing compact intervals for the global result.

Reference: lamportform.tex, Section 6, Lemma 6, Steps 8–10 (lines 617–639).
-/

namespace ConnesLean

open MeasureTheory Set Filter Metric

noncomputable section

/-! ## Helper lemmas -/

/-- Extract a proposition from ae when it does not depend on the variable.
    If `P` holds ae w.r.t. a nonzero measure, then `P` holds. -/
private theorem of_ae_of_ne_zero {μ : Measure ℝ} {Q : Prop}
    (h_ae : ∀ᵐ _ ∂μ, Q) (h_ne : μ ≠ 0) : Q := by
  haveI : NeBot (ae μ) := ae_neBot.mpr h_ne
  exact h_ae.exists.choose_spec

/-- A nonzero-measure set has nonzero restricted measure. -/
private theorem restrict_ne_zero_of_measure_ne_zero {S : Set ℝ}
    (h : volume S ≠ 0) : volume.restrict S ≠ 0 := by
  intro h_eq; apply h
  have : volume.restrict S S = 0 := by simp [h_eq]
  rwa [Measure.restrict_apply_self] at this

/-! ## Exhaustion of Ioo by Icc -/

/-- The open interval `(α, β)` is covered by the increasing sequence of compact
    intervals `[α + 1/(n+2), β - 1/(n+2)]`. -/
theorem ioo_subset_iUnion_icc {α β : ℝ} :
    Ioo α β ⊆ ⋃ n : ℕ, Icc (α + 1 / (↑n + 2)) (β - 1 / (↑n + 2)) := by
  intro x hx
  simp only [mem_iUnion, mem_Icc]
  have hxa : 0 < x - α := by linarith [hx.1]
  have hxb : 0 < β - x := by linarith [hx.2]
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / min (x - α) (β - x))
  have hmin : 0 < min (x - α) (β - x) := lt_min hxa hxb
  have hN : (0 : ℝ) < ↑n + 2 := by positivity
  have h_key : 1 / (↑n + 2) < min (x - α) (β - x) := by
    rw [div_lt_iff₀ hN]
    have h1 : 1 < min (x - α) (β - x) * ↑n := by
      rwa [div_lt_iff₀' hmin] at hn
    nlinarith [hmin]
  exact ⟨n,
    by linarith [h_key.trans_le (min_le_left _ _)],
    by linarith [h_key.trans_le (min_le_right _ _)]⟩

/-! ## Null or conull on compact subintervals -/

set_option maxHeartbeats 800000 in
-- Lebesgue differentiation + tendsto_nhds_unique need extra heartbeats
/-- On any compact `[c, d] ⊂ (α, β)`, either `B` is ae-null or ae-conull.

    Proof by contradiction: suppose both `B ∩ [c, d]` and `[c, d] \ B` have
    positive measure. By `localAverage_const_of_indicator_invariant`, the local
    average of `1_B` is constant on `[c+η, d-η]`. By `localAverage_tendsto_ae`,
    this constant converges to `1_B(x)` ae. At a point of `B`, the limit is 1;
    at a point outside `B`, it is 0. But the convergent sequence is the same,
    so `1 = 0` by `tendsto_nhds_unique`. Contradiction. -/
theorem indicator_null_or_conull_on_compact
    {B I : Set ℝ} {ε : ℝ} (h : IndicatorTranslationInvariant B I ε)
    {α β c d : ℝ} (hI : I = Ioo α β) (hαc : α < c) (hdβ : d < β) (_ : c < d) :
    volume (B ∩ Icc c d) = 0 ∨ volume (Icc c d \ B) = 0 := by
  set f := B.indicator (1 : ℝ → ℝ)
  have hf_li : LocallyIntegrable f volume :=
    (locallyIntegrable_const 1).indicator h.B_measurable
  have h_leb := localAverage_tendsto_ae f hf_li
  have h_const : ∀ η : ℝ, 0 < η →
      ∀ v, c + η ≤ v → v ≤ d - η →
        localAverage f η v = localAverage f η (c + η) :=
    fun η hη => localAverage_const_of_indicator_invariant h hI hαc hdβ hη
  -- Reference function: the local average at the moving point c + η
  set g := fun η => localAverage f η (c + η)
  -- For x ∈ (c, d), g and localAverage f · x eventually agree
  have h_eventually_eq : ∀ x ∈ Ioo c d,
      g =ᶠ[nhdsWithin 0 (Ioi 0)] (fun η => localAverage f η x) := by
    intro x hx
    have hδ : 0 < min (x - c) (d - x) :=
      lt_min (by linarith [hx.1]) (by linarith [hx.2])
    apply mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds hδ))
    intro η ⟨hη_pos, hη_small⟩
    simp only [Ioi, Iio, mem_setOf] at hη_pos hη_small
    have hη' := lt_min_iff.mp hη_small
    exact (h_const η hη_pos x (by linarith [hη'.1]) (by linarith [hη'.2])).symm
  -- Lebesgue differentiation + constancy: for ae x ∈ (c, d), g → f x
  have h_tendsto_ae : ∀ᵐ x ∂volume, x ∈ Ioo c d →
      Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds (f x)) := by
    filter_upwards [h_leb] with x hx hx_mem
    exact (Filter.tendsto_congr'
      (show g =ᶠ[nhdsWithin 0 (Ioi 0)] (fun η => localAverage f η x)
        from h_eventually_eq x hx_mem)).mpr hx
  -- Icc c d and Ioo c d differ by a null set ({c, d})
  have h_Icc_Ioo_null : volume (Icc c d \ Ioo c d) = 0 := by
    apply measure_mono_null (show Icc c d \ Ioo c d ⊆ {c, d} from by
      intro x ⟨hx_cc, hx_oo⟩
      simp only [mem_Icc, mem_Ioo, not_and_or, not_lt] at hx_cc hx_oo
      rcases hx_oo with h | h
      · exact Or.inl (le_antisymm h hx_cc.1)
      · exact Or.inr (le_antisymm hx_cc.2 h))
    have : ({c, d} : Set ℝ) = {c} ∪ {d} := by ext; simp [or_comm]
    rw [this]; exact measure_union_null Real.volume_singleton Real.volume_singleton
  -- By contradiction
  by_contra h_neither
  push_neg at h_neither
  obtain ⟨h_pos_B, h_pos_compl⟩ := h_neither
  -- Lift to open interval (Icc and Ioo differ by null set)
  have h_pos_B_open : volume (B ∩ Ioo c d) ≠ 0 := by
    intro h_zero; apply h_pos_B
    have hsub : B ∩ Icc c d ⊆ B ∩ Ioo c d ∪ (Icc c d \ Ioo c d) := by
      intro x ⟨hxB, hxI⟩
      by_cases hx : x ∈ Ioo c d
      · exact Or.inl ⟨hxB, hx⟩
      · exact Or.inr ⟨hxI, hx⟩
    exact le_antisymm (le_trans (measure_mono hsub)
      (le_trans (measure_union_le _ _) (by rw [h_zero, h_Icc_Ioo_null, zero_add])))
      (zero_le _)
  have h_pos_compl_open : volume (Ioo c d \ B) ≠ 0 := by
    intro h_zero; apply h_pos_compl
    have hsub : Icc c d \ B ⊆ Ioo c d \ B ∪ (Icc c d \ Ioo c d) := by
      intro x ⟨hxI, hxB⟩
      by_cases hx : x ∈ Ioo c d
      · exact Or.inl ⟨hx, hxB⟩
      · exact Or.inr ⟨hxI, hx⟩
    exact le_antisymm (le_trans (measure_mono hsub)
      (le_trans (measure_union_le _ _) (by rw [h_zero, h_Icc_Ioo_null, zero_add])))
      (zero_le _)
  -- On B ∩ (c, d): f = 1, so g → 1
  have h_tendsto_1 : Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    apply of_ae_of_ne_zero _ (restrict_ne_zero_of_measure_ne_zero h_pos_B_open)
    filter_upwards [ae_restrict_of_ae (s := B ∩ Ioo c d) h_tendsto_ae,
      ae_restrict_mem (μ := volume) (h.B_measurable.inter isOpen_Ioo.measurableSet)]
      with x hx hx_mem
    rw [show f x = 1 from Set.indicator_of_mem hx_mem.1 1] at hx
    exact hx hx_mem.2
  -- On (c, d) \ B: f = 0, so g → 0
  have h_tendsto_0 : Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply of_ae_of_ne_zero _ (restrict_ne_zero_of_measure_ne_zero h_pos_compl_open)
    filter_upwards [ae_restrict_of_ae (s := Ioo c d \ B) h_tendsto_ae,
      ae_restrict_mem (μ := volume) (isOpen_Ioo.measurableSet.diff h.B_measurable)]
      with x hx hx_mem
    rw [show f x = 0 from Set.indicator_of_notMem hx_mem.2 1] at hx
    exact hx hx_mem.1
  -- g → 1 and g → 0 in a Hausdorff space with NeBot filter: contradiction
  haveI : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)) := nhdsGT_neBot 0
  exact absurd (tendsto_nhds_unique h_tendsto_1 h_tendsto_0) one_ne_zero

/-! ## Main theorem -/

/-- **Lemma 6 (Null or Conull)**: If the indicator `1_B` is ae
    translation-invariant on an open interval `I`, then either `B` is
    ae-null (`volume B = 0`) or `B` is ae-conull (`volume (I \ B) = 0`).

    Proof: Pick an anchor interval `[c₀, d₀] ⊂ I`. By the compact-case
    theorem, either `B ∩ [c₀, d₀]` or `[c₀, d₀] \ B` is null. Exhaust `I`
    by increasing compact intervals `K_n ⊇ [c₀, d₀]`. For each `K_n`, the
    compact-case alternative must agree with the anchor (otherwise the anchor
    interval would have zero measure). Countable union gives the global result.

    Reference: lamportform.tex, Lemma 6 conclusion. -/
theorem null_or_conull_of_translation_invariant
    {B I : Set ℝ} {ε : ℝ}
    (h : IndicatorTranslationInvariant B I ε) :
    volume B = 0 ∨ volume (I \ B) = 0 := by
  obtain ⟨α, β, hαβ, hI⟩ := h.I_open
  -- Fix an anchor interval [c₀, d₀] strictly inside (α, β)
  set c₀ := (2 * α + β) / 3
  set d₀ := (α + 2 * β) / 3
  have hαc₀ : α < c₀ := by simp only [c₀]; linarith
  have hd₀β : d₀ < β := by simp only [d₀]; linarith
  have hc₀d₀ : c₀ < d₀ := by simp only [c₀, d₀]; linarith
  have h_vol_pos : 0 < volume (Icc c₀ d₀) := by
    rw [Real.volume_Icc]; simp; linarith [hc₀d₀]
  -- Helper: if both B ∩ [c₀, d₀] and [c₀, d₀] \ B are null, volume [c₀, d₀] = 0, contradiction
  have h_vol_absurd : ∀ (h1 : volume (B ∩ Icc c₀ d₀) = 0)
      (h2 : volume (Icc c₀ d₀ \ B) = 0), False := by
    intro h1 h2
    exact absurd (le_antisymm (le_trans (measure_mono (show Icc c₀ d₀ ⊆
      B ∩ Icc c₀ d₀ ∪ (Icc c₀ d₀ \ B) from by
        intro x hx; by_cases hxB : x ∈ B
        · exact Or.inl ⟨hxB, hx⟩
        · exact Or.inr ⟨hx, hxB⟩))
      (le_trans (measure_union_le _ _) (by rw [h1, h2, zero_add])))
      (zero_le _)) (ne_of_gt h_vol_pos)
  -- Helper: 1/(N+2) ≤ (β-α)/3 when 3/(β-α) < N
  have h_inv_le : ∀ N : ℕ, 3 / (β - α) < ↑N → 1 / (↑N + 2) ≤ (β - α) / 3 := by
    intro N hN
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ↑N + 2) (by norm_num : (0:ℝ) < 3)]
    have : 3 < (β - α) * ↑N := by rwa [div_lt_iff₀' (by linarith : 0 < β - α)] at hN
    nlinarith [show 0 < β - α from by linarith]
  -- Apply compact lemma to anchor
  rcases indicator_null_or_conull_on_compact h hI hαc₀ hd₀β hc₀d₀
    with h_null | h_conull
  · -- Case 1: volume (B ∩ [c₀, d₀]) = 0 → volume B = 0
    left
    -- Exhausting sequence K_n = Icc (α + 1/(n+2)) (β - 1/(n+2))
    set K : ℕ → Set ℝ := fun n => Icc (α + 1 / (↑n + 2)) (β - 1 / (↑n + 2))
    -- B ⊆ I ⊆ ⋃ K_n
    have hB_sub : B ⊆ ⋃ n, B ∩ K n := by
      intro x hx
      have hxI := h.B_subset hx
      rw [hI] at hxI
      obtain ⟨n, hn⟩ := mem_iUnion.mp (ioo_subset_iUnion_icc hxI)
      exact mem_iUnion.mpr ⟨n, hx, hn⟩
    -- For each n, volume (B ∩ K_n) = 0
    suffices h_each : ∀ n, volume (B ∩ K n) = 0 from
      le_antisymm (le_trans (measure_mono hB_sub)
        (le_trans (measure_iUnion_le _) (by simp [h_each]))) (zero_le _)
    intro n
    -- Helper: K_n monotonicity (n ≤ m → K n ⊆ K m)
    have hK_mono : ∀ n m : ℕ, n ≤ m → K n ⊆ K m := by
      intro n m hnm
      apply Icc_subset_Icc
      · gcongr
      · gcongr
    -- Find N₀ such that [c₀, d₀] ⊆ K_{N₀}
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (3 / (β - α))
    have h_anchor_sub : Icc c₀ d₀ ⊆ K N₀ := by
      apply Icc_subset_Icc
      · simp only [c₀]; linarith [h_inv_le N₀ hN₀]
      · simp only [d₀]; linarith [h_inv_le N₀ hN₀]
    -- Helper: apply compact lemma to K_n when non-degenerate
    have hK_apply : ∀ m : ℕ, Icc c₀ d₀ ⊆ K m →
        α + 1/(↑m+2) < β - 1/(↑m+2) → volume (B ∩ K m) = 0 := by
      intro m h_sub hm
      rcases indicator_null_or_conull_on_compact h hI
        (by linarith [show (0:ℝ) < 1/(↑m+2) from by positivity])
        (by linarith [show (0:ℝ) < 1/(↑m+2) from by positivity]) hm
        with h | h
      · exact h
      · exact (h_vol_absurd h_null (measure_mono_null (diff_subset_diff_left h_sub) h)).elim
    -- vol(B ∩ K_{N₀}) = 0
    have h_N₀_null : volume (B ∩ K N₀) = 0 := by
      by_cases hK_degen : β - 1 / (↑N₀ + 2) ≤ α + 1 / (↑N₀ + 2)
      · exact measure_mono_null inter_subset_right
          (by simp only [K, Real.volume_Icc]; exact ENNReal.ofReal_of_nonpos (by linarith))
      · push_neg at hK_degen
        exact hK_apply N₀ h_anchor_sub hK_degen
    -- For any n: vol(B ∩ K_n) = 0
    by_cases hn_le : n ≤ N₀
    · -- K_n ⊆ K_{N₀}
      exact measure_mono_null (inter_subset_inter_right B (hK_mono n N₀ hn_le)) h_N₀_null
    · -- K_{N₀} ⊆ K_n
      push_neg at hn_le
      by_cases hK_degen : β - 1 / (↑n + 2) ≤ α + 1 / (↑n + 2)
      · exact measure_mono_null inter_subset_right
          (by simp only [K, Real.volume_Icc]; exact ENNReal.ofReal_of_nonpos (by linarith))
      · push_neg at hK_degen
        exact hK_apply n (le_trans h_anchor_sub (hK_mono N₀ n (le_of_lt hn_le)))
          hK_degen
  · -- Case 2: volume ([c₀, d₀] \ B) = 0 → volume (I \ B) = 0
    right
    set K : ℕ → Set ℝ := fun n => Icc (α + 1 / (↑n + 2)) (β - 1 / (↑n + 2))
    have hI_sub : I \ B ⊆ ⋃ n, K n \ B := by
      intro x ⟨hxI, hxB⟩
      rw [hI] at hxI
      obtain ⟨n, hn⟩ := mem_iUnion.mp (ioo_subset_iUnion_icc hxI)
      exact mem_iUnion.mpr ⟨n, hn, hxB⟩
    suffices h_each : ∀ n, volume (K n \ B) = 0 from
      le_antisymm (le_trans (measure_mono hI_sub)
        (le_trans (measure_iUnion_le _) (by simp [h_each]))) (zero_le _)
    intro n
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (3 / (β - α))
    have h_anchor_sub : Icc c₀ d₀ ⊆ K N₀ := by
      apply Icc_subset_Icc
      · simp only [c₀]; linarith [h_inv_le N₀ hN₀]
      · simp only [d₀]; linarith [h_inv_le N₀ hN₀]
    -- Helper: apply compact lemma and use h_vol_absurd when null branch contradicts
    have hK_apply_conull : ∀ m : ℕ, Icc c₀ d₀ ⊆ K m →
        α + 1/(↑m+2) < β - 1/(↑m+2) → volume (K m \ B) = 0 := by
      intro m h_sub hm
      rcases indicator_null_or_conull_on_compact h hI
        (by linarith [show (0:ℝ) < 1/(↑m+2) from by positivity])
        (by linarith [show (0:ℝ) < 1/(↑m+2) from by positivity]) hm
        with h | h
      · exact (h_vol_absurd (measure_mono_null (inter_subset_inter_right B h_sub) h)
            h_conull).elim
      · exact h
    have h_N₀_conull : volume (K N₀ \ B) = 0 := by
      by_cases hK_degen : β - 1 / (↑N₀ + 2) ≤ α + 1 / (↑N₀ + 2)
      · exact measure_mono_null diff_subset
          (by simp only [K, Real.volume_Icc]; exact ENNReal.ofReal_of_nonpos (by linarith))
      · push_neg at hK_degen
        exact hK_apply_conull N₀ h_anchor_sub hK_degen
    by_cases hn_le : n ≤ N₀
    · have h_sub : K n ⊆ K N₀ := by
        apply Icc_subset_Icc <;> gcongr
      exact measure_mono_null (diff_subset_diff_left h_sub) h_N₀_conull
    · push_neg at hn_le
      by_cases hK_degen : β - 1 / (↑n + 2) ≤ α + 1 / (↑n + 2)
      · exact measure_mono_null diff_subset
          (by simp only [K, Real.volume_Icc]; exact ENNReal.ofReal_of_nonpos (by linarith))
      · push_neg at hK_degen
        have h_sub : K N₀ ⊆ K n := by
          apply Icc_subset_Icc <;> gcongr
        exact hK_apply_conull n (le_trans h_anchor_sub h_sub) hK_degen

end

end ConnesLean
