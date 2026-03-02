/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Inversion Symmetry & Even Ground State — Corollary 16

Reference: lamportform.tex, Corollary 16 (lines 1559–1676).

The ground-state eigenfunction ψ satisfies ψ(-u) = ψ(u) a.e. (evenness).

One axiom:
1. `resolvent_commutes_reflection`: resolvent commutes with reflection (Prop 14)

## Main results

- `reflectionOp`: defines (Rφ)(u) = φ(-u)
- `resolvent_commutes_reflection`: axiom — resolvent commutes with reflection a.e.
- `reflection_eigenfunction`: R(ψ) is a resolvent eigenfunction
- `ground_state_even`: ψ(-u) = ψ(u) a.e.
-/

import ConnesLean.Stage7.GroundState

/-!
# Inversion Symmetry & Even Ground State

Formalizes Corollary 16: the ground-state eigenfunction is even.

Reference: lamportform.tex, lines 1559–1676.
-/

namespace ConnesLean

open MeasureTheory Set Real Filter

noncomputable section

/-! ## Section 1: Reflection operator -/

/-- Reflection operator: (Rφ)(u) = φ(-u). -/
def reflectionOp (φ : ℝ → ℂ) : ℝ → ℂ := fun u => φ (-u)

@[simp] theorem reflectionOp_apply (φ : ℝ → ℂ) (u : ℝ) :
    reflectionOp φ u = φ (-u) := rfl

@[simp] theorem reflectionOp_reflectionOp (φ : ℝ → ℂ) :
    reflectionOp (reflectionOp φ) = φ := by ext u; simp [reflectionOp, neg_neg]

/-! ## Section 2: Symmetric interval and ae helper -/

theorem logInterval_neg_mem {L : ℝ} {x : ℝ} (hx : x ∈ logInterval L) :
    -x ∈ logInterval L := by
  simp only [logInterval, mem_Ioo] at hx ⊢
  constructor <;> linarith

/-- Almost-everywhere transfer through negation: if f =ᵐ g then
    f ∘ Neg.neg =ᵐ g ∘ Neg.neg, using the neg-invariance of Lebesgue measure. -/
theorem ae_neg {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    (fun x => f (-x)) =ᵐ[volume] (fun x => g (-x)) := by
  rw [Filter.EventuallyEq, ae_iff] at h ⊢
  have heq : {x : ℝ | f (-x) ≠ g (-x)} = Neg.neg ⁻¹' {x : ℝ | f x ≠ g x} := by
    ext x; simp
  rw [heq]
  have : Neg.neg ⁻¹' {x : ℝ | f x ≠ g x} =
      (fun x => (-1 : ℝ) * x) ⁻¹' {x : ℝ | f x ≠ g x} := by
    ext x; simp
  rw [this, Real.volume_preimage_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]
  simp [h]

/-! ## Section 3: Resolvent-reflection axiom -/

/-- **Resolvent commutes with reflection (Proposition 14).**
    The resolvent (A_λ + I)⁻¹ commutes with the reflection operator R
    defined by (Rφ)(u) = φ(-u).

    The mathematical argument (lamportform.tex, lines 1559–1618):
    1. The energy form satisfies E(Rφ, Rψ) = E(φ, ψ) (reflection invariance)
    2. By polarization and the Kato representation theorem, the operator
       A_λ commutes with R
    3. Therefore the resolvent (A_λ + I)⁻¹ commutes with R

    **Why axiom:** Steps 1-3 require bilinear form polarization identity,
    Kato representation theorem, and resolvent functional calculus — none
    in Mathlib.

    **Soundness:** Sole precondition `1 < cutoffLambda`. Conclusion is a
    nontrivial a.e. equality between two function compositions that cannot
    be vacuously satisfied. Precondition: `1 < cutoffLambda`. -/
axiom resolvent_commutes_reflection (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (φ : ℝ → ℂ) :
    ∀ᵐ x ∂volume,
      (kato_operator cutoffLambda hLam).resolvent (reflectionOp φ) x =
      reflectionOp ((kato_operator cutoffLambda hLam).resolvent φ) x

/-- Almost-everywhere transfer of predicates through negation: if P holds a.e.
    then P ∘ Neg.neg holds a.e. -/
theorem ae_of_ae_neg {P : ℝ → Prop} (h : ∀ᵐ x ∂(volume : Measure ℝ), P x) :
    ∀ᵐ x ∂(volume : Measure ℝ), P (-x) := by
  rw [ae_iff] at h ⊢
  have heq : {x : ℝ | ¬P (-x)} = Neg.neg ⁻¹' {x : ℝ | ¬P x} := by ext x; simp
  rw [heq]
  have : Neg.neg ⁻¹' {x : ℝ | ¬P x} =
      (fun x => (-1 : ℝ) * x) ⁻¹' {x : ℝ | ¬P x} := by ext x; simp
  rw [this, Real.volume_preimage_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]
  simp [h]

/-! ## Section 4: Reflected eigenfunction is eigenfunction -/

/-- The reflected ground-state eigenfunction R(ψ) satisfies the same resolvent
    eigenvalue equation as ψ. This chains the resolvent-reflection axiom with
    the ground-state resolvent eigenvalue equation transferred through negation. -/
theorem reflection_eigenfunction (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    let gs := ground_state_exists cutoffLambda hLam
    let T := kato_operator cutoffLambda hLam
    ∀ᵐ x ∂volume,
      T.resolvent (reflectionOp gs.eigenfunction) x =
        ((1 : ℝ) / (gs.eigenvalue + 1)) • reflectionOp gs.eigenfunction x := by
  intro gs T
  -- h1: T.resolvent(R ψ)(x) =ᵐ R(T.resolvent ψ)(x)  (axiom)
  have h1 := resolvent_commutes_reflection cutoffLambda hLam gs.eigenfunction
  -- h2: (T.resolvent ψ)(-x) =ᵐ (1/(μ₀+1))•ψ(-x)  (ae_neg of eigenvalue eq)
  have h2 := ae_neg gs.resolvent_eigenvalue
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [one_div, reflectionOp_apply, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_add, Complex.ofReal_one] at hx1 hx2 ⊢
  rw [hx1, hx2]

/-! ## Section 5: Even ground state -/

/-- Helper: derive False from an ae statement that implies every point of a
    nonempty open interval leads to a contradiction. -/
private theorem false_of_ae_false_on_logInterval (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (h : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ logInterval (Real.log cutoffLambda) → False) :
    False := by
  have h_vol : volume (logInterval (Real.log cutoffLambda)) = 0 := by
    rw [ae_iff] at h
    have : {x : ℝ | ¬(x ∈ logInterval (Real.log cutoffLambda) → False)} =
        logInterval (Real.log cutoffLambda) := by ext x; simp
    rw [← this]; exact h
  have h_pos_vol : (0 : ENNReal) < volume (logInterval (Real.log cutoffLambda)) := by
    rw [logInterval, Real.volume_Ioo]; simp [ENNReal.ofReal_pos]; linarith [Real.log_pos hLam]
  exact absurd h_vol (ne_of_gt h_pos_vol)

/-- **Ground state is even (Corollary 16).**
    The ground-state eigenfunction ψ satisfies ψ(-u) = ψ(u) a.e.

    Reference: lamportform.tex, Corollary 16 (lines 1648–1676). -/
theorem ground_state_even (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    reflectionOp (ground_state_exists cutoffLambda hLam).eigenfunction
      =ᵐ[volume] (ground_state_exists cutoffLambda hLam).eigenfunction := by
  set gs := ground_state_exists cutoffLambda hLam with gs_def
  -- Step 1: R(ψ) is a resolvent eigenfunction, so by simplicity R(ψ) =ᵐ c•ψ
  have h_refl_eigen : ∀ᵐ x ∂volume,
      (kato_operator cutoffLambda hLam).resolvent (reflectionOp gs.eigenfunction) x =
        ((1 : ℝ) / (gs.eigenvalue + 1)) • reflectionOp gs.eigenfunction x := by
    rw [gs_def]; exact reflection_eigenfunction cutoffLambda hLam
  obtain ⟨c, hc⟩ := gs.eigenvalue_simple (reflectionOp gs.eigenfunction) h_refl_eigen
  -- hc: ∀ᵐ x, (gs.eigenfunction)(-x) = c • gs.eigenfunction x
  -- Step 2: Apply ae_neg to get ψ = c²•ψ a.e.
  have h_sq : ∀ᵐ x ∂volume, gs.eigenfunction x = (c ^ 2) • gs.eigenfunction x := by
    filter_upwards [ae_neg hc, hc] with x hx_neg hx
    -- hx_neg: (reflectionOp gs.eigenfunction)(-x) = c • gs.eigenfunction (-x)
    -- hx:     (reflectionOp gs.eigenfunction)(x) = c • gs.eigenfunction x
    simp only [reflectionOp_apply, neg_neg] at hx_neg
    -- hx_neg: gs.eigenfunction x = c • gs.eigenfunction (-x)
    simp only [reflectionOp_apply] at hx
    -- hx: gs.eigenfunction (-x) = c • gs.eigenfunction x
    calc gs.eigenfunction x = c • gs.eigenfunction (-x) := hx_neg
      _ = c • (c • gs.eigenfunction x) := by rw [hx]
      _ = (c ^ 2) • gs.eigenfunction x := by rw [smul_smul, sq]
  -- Step 3: Extract c² = 1
  have hc_sq : c ^ 2 = 1 := by
    by_contra h_ne
    have h_zero : ∀ᵐ x ∂volume, gs.eigenfunction x = 0 := by
      filter_upwards [h_sq] with x hx
      have : (c ^ 2 - 1) • gs.eigenfunction x = 0 := by
        rw [sub_smul, one_smul, sub_eq_zero]; exact hx.symm
      exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h_ne)
    exact false_of_ae_false_on_logInterval cutoffLambda hLam (by
      filter_upwards [h_zero, gs.eigenfunction_pos_ae] with x hx_zero hx_pos hx_mem
      exact absurd (hx_zero ▸ (rfl : (0 : ℂ).re = 0) ▸ le_refl (0 : ℝ))
        (not_le.mpr (hx_pos hx_mem)))
  -- Step 4: c = 1 or c = -1
  rcases sq_eq_one_iff.mp hc_sq with rfl | rfl
  · -- Case c = 1: R(ψ) =ᵐ 1•ψ = ψ ✓
    filter_upwards [hc] with x hx
    simp only [reflectionOp_apply, one_smul] at hx; exact hx
  · -- Case c = -1: contradiction with positivity
    exfalso
    exact false_of_ae_false_on_logInterval cutoffLambda hLam (by
      filter_upwards [hc, gs.eigenfunction_pos_ae,
          ae_of_ae_neg gs.eigenfunction_pos_ae] with x hx hx_pos hx_pos_neg hx_mem
      have h1 : 0 < (gs.eigenfunction x).re := hx_pos hx_mem
      have h2 : 0 < (gs.eigenfunction (-x)).re := hx_pos_neg (logInterval_neg_mem hx_mem)
      simp only [reflectionOp_apply, neg_smul, one_smul] at hx
      rw [hx] at h2; simp only [Complex.neg_re] at h2; linarith)

/-! ## Section 6: Soundness tests -/

-- Test 1: ground_state_even composes correctly
example (Λ : ℝ) (hΛ : 1 < Λ) :
    reflectionOp (ground_state_exists Λ hΛ).eigenfunction
      =ᵐ[volume] (ground_state_exists Λ hΛ).eigenfunction :=
  ground_state_even Λ hΛ

-- Test 2: reflectionOp is an involution
example (φ : ℝ → ℂ) : reflectionOp (reflectionOp φ) = φ :=
  reflectionOp_reflectionOp φ

-- Test 3: logInterval is symmetric
example (L x : ℝ) (hx : x ∈ logInterval L) : -x ∈ logInterval L :=
  logInterval_neg_mem hx

end

end ConnesLean
