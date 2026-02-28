/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Translation-Invariance Setup for Indicator Functions

Reference: lamportform.tex, Section 6, Lemma 6, Steps 1–3 (lines 542–576).

This file defines the hypothesis that an indicator `1_B` is ae translation-invariant
on an open interval `I`, and reduces the ae statement from `I ∩ (I+t)` to compact
subintervals `J ⊂⊂ I`.

The key steps:
1. For `J = Icc a b ⊆ Ioo α β = I`, the margin `δ₀ = min(a - α, β - b) > 0`.
2. For `t ∈ (0, δ₀)`, `J ⊆ I ∩ preimage (·-t) I`, so the ae hypothesis transfers.
3. Quantification over all small `t` yields ae shift-invariance on `J`.
-/

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Translation-Invariance Setup for Indicator Functions

Defines the hypothesis that an indicator `1_B` is ae translation-invariant on an open
interval `I`, and reduces the ae statement from `I ∩ (I+t)` to compact subintervals
`J ⊂⊂ I` using the margin `δ₀ = min(a - α, β - b)`.

Reference: lamportform.tex, Section 6, Lemma 6, Steps 1–3 (lines 542–576).
-/

namespace ConnesLean

open MeasureTheory Set Filter

noncomputable section

/-! ## Hypothesis definition -/

/-- The indicator `1_B` is ae translation-invariant on an open interval `I`.

    Concretely: `B ⊆ I`, `I` is an open interval `Ioo α β`, and for all
    `t ∈ (0, ε)`, the indicator `1_B` satisfies `1_B(u) = 1_B(u - t)` a.e. on
    the overlap `I ∩ preimage (· - t) I`.

    Reference: lamportform.tex, Lemma 6 hypothesis. -/
structure IndicatorTranslationInvariant (B I : Set ℝ) (ε : ℝ) : Prop where
  ε_pos : 0 < ε
  B_measurable : MeasurableSet B
  B_subset : B ⊆ I
  I_open : ∃ α β, α < β ∧ I = Ioo α β
  ae_shift : ∀ t, 0 < t → t < ε →
    ∀ᵐ u ∂(volume.restrict (I ∩ preimage (· - t) I)),
      B.indicator (1 : ℝ → ℝ) u = B.indicator (1 : ℝ → ℝ) (u - t)

/-! ## Margin of compact subinterval -/

/-- The margin of `Icc a b` inside `Ioo α β`: `δ₀ = min(a - α, β - b)`.
    Positive when `α < a` and `b < β`, i.e. `Icc a b ⊆ Ioo α β` with room to spare. -/
def compactMargin (α β a b : ℝ) : ℝ := min (a - α) (β - b)

/-- The margin is positive when `Icc a b` sits strictly inside `Ioo α β`. -/
theorem compactMargin_pos {α β a b : ℝ} (hαa : α < a) (hbβ : b < β) :
    0 < compactMargin α β a b := by
  simp only [compactMargin, lt_min_iff]
  exact ⟨by linarith, by linarith⟩

/-! ## Subset containment under shifts -/

/-- For `t < δ₀`, the compact interval `Icc a b` is contained in
    `Ioo α β ∩ preimage (·-t) (Ioo α β)`. This means both `u ∈ I` and
    `u - t ∈ I` for every `u ∈ J`. -/
theorem icc_subset_ioo_inter_shift {α β a b t : ℝ}
    (hαa : α < a) (hbβ : b < β)
    (ht_pos : 0 < t) (ht_bound : t < compactMargin α β a b) :
    Icc a b ⊆ Ioo α β ∩ preimage (· - t) (Ioo α β) := by
  intro u hu
  have hδ₁ : t < a - α := lt_of_lt_of_le ht_bound (min_le_left _ _)
  have hδ₂ : t < β - b := lt_of_lt_of_le ht_bound (min_le_right _ _)
  exact ⟨Icc_subset_Ioo hαa hbβ hu,
         mem_preimage.mpr (mem_Ioo.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)⟩

/-! ## Restricting the ae hypothesis to compact subintervals -/

/-- **Step 2**: The ae shift-invariance transfers from `I ∩ (I+t)` to any
    compact `J = Icc a b ⊆ I` when `t` is small enough.

    Given the `IndicatorTranslationInvariant` hypothesis, for any compact
    `Icc a b` with `α < a`, `b < β` (where `I = Ioo α β`), and any
    `t ∈ (0, min(ε, δ₀))`:

    `1_B(u) = 1_B(u - t)` a.e. on `Icc a b`.

    Reference: lamportform.tex, Lemma 6, Step 2. -/
theorem indicator_ae_shift_on_compact
    {B I : Set ℝ} {ε : ℝ} (h : IndicatorTranslationInvariant B I ε)
    {α β a b : ℝ} (hI : I = Ioo α β) (hαa : α < a) (hbβ : b < β)
    {t : ℝ} (ht_pos : 0 < t) (ht_ε : t < ε)
    (ht_δ : t < compactMargin α β a b) :
    ∀ᵐ u ∂(volume.restrict (Icc a b)),
      B.indicator (1 : ℝ → ℝ) u = B.indicator (1 : ℝ → ℝ) (u - t) := by
  have h_sub : Icc a b ⊆ I ∩ preimage (· - t) I := by
    rw [hI]
    exact icc_subset_ioo_inter_shift hαa hbβ ht_pos ht_δ
  exact ae_restrict_of_ae_restrict_of_subset h_sub (h.ae_shift t ht_pos ht_ε)

/-- **Step 3**: Quantified version — the ae shift-invariance holds for all
    sufficiently small positive `t`, on any compact `Icc a b ⊆ I`.

    The threshold is `δ = min(ε, compactMargin α β a b)`. -/
theorem indicator_ae_shift_forall_small
    {B I : Set ℝ} {ε : ℝ} (h : IndicatorTranslationInvariant B I ε)
    {α β a b : ℝ} (hI : I = Ioo α β) (hαa : α < a) (hbβ : b < β) :
    let δ := min ε (compactMargin α β a b)
    0 < δ ∧ ∀ t, 0 < t → t < δ →
      ∀ᵐ u ∂(volume.restrict (Icc a b)),
        B.indicator (1 : ℝ → ℝ) u = B.indicator (1 : ℝ → ℝ) (u - t) := by
  refine ⟨lt_min h.ε_pos (compactMargin_pos hαa hbβ), fun t ht_pos ht_δ => ?_⟩
  exact indicator_ae_shift_on_compact h hI hαa hbβ ht_pos
    (lt_of_lt_of_le ht_δ (min_le_left _ _))
    (lt_of_lt_of_le ht_δ (min_le_right _ _))

end

end ConnesLean
