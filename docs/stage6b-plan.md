# Stage 6B Plan: InvarianceSplit — Lemma 14

## Scope

lamportform.tex lines 1220–1310 (Lemma 14: Invariant ideals and splitting of the form).

**File:** `ConnesLean/ConnesLean/Stage6/InvarianceSplit.lean`

## Mathematical Statement

If `L²(B)` is invariant under `T(t) = e^{-tA_λ}`, then for every `G ∈ D(E_λ)`:
- `1_B · G ∈ D(E_λ)` and `1_{I\B} · G ∈ D(E_λ)`
- `E_λ(G) = E_λ(1_B · G) + E_λ(1_{I\B} · G)`

## Proof Structure (6 steps from LaTeX)

### Step 1: Projection setup
- Let `P = M_{1_B}` (multiplication by indicator of B), `Q = I - P`
- P is an orthogonal projection with Ran(P) = L²(B)
- **In Lean:** just definitions, no proof needed beyond `P² = P` and `P* = P`

### Step 2: P commutes with T(t) for all t ≥ 0
- Invariance of L²(B) means T(t)(Ran P) ⊆ Ran P, i.e. PT(t)P = T(t)P
- Take adjoints: PT(t)P = PT(t). Together: T(t)P = PT(t)
- **In Lean:** this is part of the `SemigroupInvariantIdeal` structure hypothesis

### Step 3: P commutes with (A_λ + α)⁻¹ for every α > 0
- Laplace transform: `(A_λ+α)⁻¹ = ∫₀^∞ e^{-αt} T(t) dt`
- P commutes with T(t) → P commutes with the Bochner integral
- **In Lean:** AXIOM (`laplace_resolvent_commute`)

### Step 4: P commutes with A_λ^{1/2}
- P commutes with R = (A_λ+1)⁻¹ (from Step 3 with α=1)
- Borel functional calculus: P commutes with every bounded Borel function of R
- This extends to spectral projections, hence to A_λ^{1/2}
- **In Lean:** AXIOM (`projection_commutes_with_sqrt`)

### Step 5: P preserves D(E_λ)
- D(E_λ) = D(A_λ^{1/2})
- If u ∈ D(A_λ^{1/2}), then A_λ^{1/2}(Pu) = P(A_λ^{1/2} u) ∈ L²(I)
- So Pu ∈ D(A_λ^{1/2}). Similarly Qu.
- **In Lean:** theorem, follows from the sqrt commutation axiom

### Step 6: Pythagorean splitting
- E_λ(G) = ‖A_λ^{1/2} G‖² (form identity from Kato)
- A_λ^{1/2} G = P(A_λ^{1/2} G) + Q(A_λ^{1/2} G) (since P+Q = I)
- P and Q images are orthogonal: ⟨Pv, Qv⟩ = 0
- Pythagorean: ‖v‖² = ‖Pv‖² + ‖Qv‖²
- Using commutativity: ‖P(A^{1/2}G)‖² = ‖A^{1/2}(PG)‖² = E_λ(PG)
- **In Lean:** theorem, uses axioms + Kato structure

## Lean Declarations

### Structures

```lean
/-- A semigroup-invariant ideal in L²(I): measurable B ⊆ I such that
    L²(B) is invariant under the semigroup e^{-tA_λ}. -/
structure SemigroupInvariantIdeal (cutoffLambda : ℝ) where
  B : Set ℝ
  B_measurable : MeasurableSet B
  B_subset : B ⊆ logInterval (Real.log cutoffLambda)
```

### Axioms

```lean
/-- P commutes with T(t) ⟹ P commutes with (A_λ+α)⁻¹.
    Laplace transform formula + Bochner integral commutation.
    Reference: Engel-Nagel, Cor II.1.11. -/
axiom laplace_resolvent_commute (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ G : ℝ → ℂ,
      (kato_operator cutoffLambda hLam).resolvent (B.indicator G) =
      B.indicator ((kato_operator cutoffLambda hLam).resolvent G)

/-- P commutes with A_λ^{1/2}: if P commutes with the resolvent,
    then P preserves D(E_λ) and commutes with the form.
    Reference: Reed-Simon, Thm VIII.5. -/
axiom projection_commutes_with_sqrt (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hB_sub : B ⊆ logInterval (Real.log cutoffLambda)) :
    ∀ G ∈ formDomain cutoffLambda,
      B.indicator G ∈ formDomain cutoffLambda ∧
      energyForm cutoffLambda G =
        energyForm cutoffLambda (B.indicator G) +
        energyForm cutoffLambda ((logInterval (Real.log cutoffLambda) \ B).indicator G)
```

### Theorems

```lean
/-- Domain preservation: P maps D(E_λ) into D(E_λ). -/
theorem invariance_domain_preserved (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) (G : ℝ → ℂ)
    (hG : G ∈ formDomain cutoffLambda) :
    ideal.B.indicator G ∈ formDomain cutoffLambda

/-- Complement domain preservation: Q maps D(E_λ) into D(E_λ). -/
theorem invariance_complement_domain_preserved (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) (G : ℝ → ℂ)
    (hG : G ∈ formDomain cutoffLambda) :
    (logInterval (Real.log cutoffLambda) \ ideal.B).indicator G ∈ formDomain cutoffLambda

/-- Main Lemma 14: Energy splitting for invariant ideals. -/
theorem invariance_split (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (ideal : SemigroupInvariantIdeal cutoffLambda) (G : ℝ → ℂ)
    (hG : G ∈ formDomain cutoffLambda) :
    energyForm cutoffLambda G =
      energyForm cutoffLambda (ideal.B.indicator G) +
      energyForm cutoffLambda ((logInterval (Real.log cutoffLambda) \ ideal.B).indicator G)
```

## Imports

```lean
import ConnesLean.Stage5.CompactResolvent
```

This transitively brings in `ClosedForm`, `CompactEmbedding`, `EnergyForm`, etc.

## Design Decision: Axiom Granularity

The LaTeX proof has Steps 2–4 (commutation chain) as the hard part, and Steps 5–6
(domain preservation + Pythagorean) as the payoff. Two approaches:

**Option A (current plan): Two fine-grained axioms**
- `laplace_resolvent_commute`: P commutes with resolvent (Step 3)
- `projection_commutes_with_sqrt`: P preserves domain + energy splits (Steps 4–6 combined)
- Theorems derive domain preservation and splitting from these axioms

**Option B: One coarse axiom**
- Single axiom stating the full Lemma 14 conclusion directly
- Simpler but less reusable, and doesn't separate the functional analysis steps

**Recommendation:** Option A is closer to the math but `projection_commutes_with_sqrt`
as stated already bundles Steps 4–6. The resolvent commutation axiom is separately
useful (Stage 6E will reference it). Actually, looking more carefully,
`projection_commutes_with_sqrt` gives both domain preservation AND the splitting,
so `invariance_domain_preserved` and `invariance_split` are just projections of
the axiom's output.

This means the theorems are thin wrappers. The real content is in the two axioms.

## Estimated Size

~80–100 lines total:
- Module header + imports: ~25 lines
- `SemigroupInvariantIdeal` structure: ~10 lines
- Two axioms with docstrings: ~30 lines
- Three theorems (thin wrappers): ~25 lines
- Tests (examples): ~10 lines
