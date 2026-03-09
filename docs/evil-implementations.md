# Evil Implementations of `energyForm`

This document describes three "wrong but plausible" implementations of
`energyForm` and checks whether the existing formalized spec rules each one out.

Reference: the real definition lives in
`ConnesLean/Stage2/EnergyForm.lean:57`.

---

## Evil 1: The Zero Form

> "An energy form that always returns zero."

```lean
def energyForm_evil1 (_cutoffLambda : ℝ) (_G : ℝ → ℂ) : ENNReal := 0
```

**Why it looks plausible.** It satisfies:
- `energyForm_nonneg`: 0 ≥ 0. ✓
- `energyForm_zero`: E_λ(0) = 0. ✓
- `totalCorrection_prime_nonpos`: unaffected (separate definition). ✓
- `energyForm_comp_normalContraction_le` (Markov): 0 ≤ 0. ✓
- `energyForm_abs_le`: 0 ≤ 0. ✓

**What rules it out.**
`energyForm_one_pos` (`Stage6/EnergyPositivity.lean:115`):
for λ > 1, E_λ(1) > 0. The zero form gives E_λ(1) = 0, contradiction.

Also `energyForm_indicator_null` (`Stage6/EnergyPositivity.lean:220`):
if E_λ(1_B) = 0 implies m(B) = 0, then taking B = I gives E_λ(1_I) = 0 ⟹
m(I) = 0, but I = (−log λ, log λ) has positive measure for λ > 1.

**Verdict: RULED OUT** by `energyForm_one_pos`. ✓

---

## Evil 2: The Constant Form

> "An energy form that returns the same positive constant for every nonzero function."

```lean
def energyForm_evil2 (cutoffLambda : ℝ) (G : ℝ → ℂ) : ENNReal :=
  if G = 0 then 0 else 1
```

**Why it looks plausible.** It satisfies:
- `energyForm_nonneg`: values are 0 or 1, both ≥ 0. ✓
- `energyForm_zero`: E_λ(0) = 0. ✓
- `energyForm_one_pos`: E_λ(1) = 1 > 0. ✓
- `energyForm_abs_le`: for G ≠ 0, |G| ≠ 0, so 1 ≤ 1. ✓

**What rules it out.**
`energyForm_indicator_null` (`Stage6/EnergyPositivity.lean:220`):
Take any measurable B ⊆ I with 0 < m(B) < m(I). Then 1_B ≠ 0 so
E_λ(1_B) = 1 ≠ 0, which is fine so far. But consider:

`energyForm_indicator_add_le` (Proposition 10, `Stage6/NormInequality.lean:234`):
E_λ(1) ≤ E_λ(1_B) + E_λ(1_{I\B}). Under Evil 2, this becomes 1 ≤ 1 + 1 = 2. ✓
That alone doesn't kill it.

The real kill comes from the **Fourier representation** axiom
(`energyForm_eq_fourierSymbol_integral`, `Stage5/ClosedForm.lean:90`):
E_λ(G) = (1/2π) ∫ ψ_λ(ξ) |Ĝ(ξ)|² dξ. For G = c·1_I (varying c ≠ 0),
the Fourier integral scales as |c|². Evil 2 gives E_λ(c·1_I) = 1 for all
c ≠ 0, violating quadratic scaling. Concretely, if G and 2G are both nonzero,
the Fourier representation gives E_λ(2G) = 4·E_λ(G), but Evil 2 gives
E_λ(2G) = 1 = E_λ(G).

**Verdict: RULED OUT** by `energyForm_eq_fourierSymbol_integral` (quadratic scaling). ✓

---

## Evil 3: The L²-Norm Form

> "An energy form that is just the L² norm squared — ignoring all translation structure."

```lean
def energyForm_evil3 (_cutoffLambda : ℝ) (G : ℝ → ℂ) : ENNReal :=
  ‖G‖₂²
```

**Why it looks plausible.** It satisfies:
- `energyForm_nonneg`: ‖G‖₂² ≥ 0. ✓
- `energyForm_zero`: ‖0‖₂² = 0. ✓
- `energyForm_one_pos`: ‖1_I‖₂² = m(I) > 0 for λ > 1. ✓
- `energyForm_abs_le`: ‖|G|‖₂ = ‖G‖₂. ✓
- Fourier representation: ‖G‖₂² = (1/2π) ∫ |Ĝ(ξ)|² dξ by Plancherel,
  so this corresponds to ψ_λ(ξ) ≡ 1. ✓ (structurally valid)

This is the most dangerous evil implementation — it passes many checks.

**What rules it out.**
The **Markov property** theorem `energyForm_comp_normalContraction_le`
(`Stage4/MarkovProperty.lean:137`) states E_λ(Φ ∘ G) ≤ E_λ(G) for normal
contractions. For the L² norm this holds (contractions don't increase norm). ✓

However, the **closedness axiom** `energyForm_closed_on_line`
(`Stage5/ClosedForm.lean:136`) returns an `IsClosedEnergyForm` structure whose
`smooth_in_domain` field requires that every smooth compactly-supported G has
finite energy, and whose `graph_complete` field requires completeness in the
**graph norm** ‖G‖₂² + E_λ(G). For ψ_λ ≡ 1, the graph norm is just 2‖G‖₂²,
and the form domain is all of L². This would make the resolvent the identity
(up to scaling), which is **not compact**.

The spec demands compact resolvent via `kato_operator`
(`Stage5/ClosedForm.lean` axiom) which constructs a self-adjoint operator
whose resolvent is compact. The L²-norm form generates a bounded operator
(a scalar multiple of the identity), whose resolvent (λ−c)⁻¹·Id is bounded
but **not compact** on infinite-dimensional L²(I). This contradicts the
compact-resolvent property required downstream.

Additionally, the Fourier symbol axiom requires ψ_λ(ξ) to satisfy the
logarithmic lower bound `fourierSymbol_ge_log`: ψ_λ(ξ) ≥ C · log(1 + ξ²).
The constant symbol ψ_λ ≡ 1 violates this for large |ξ|.

**Verdict: RULED OUT** by `fourierSymbol_ge_log` (logarithmic growth) and
compact resolvent. ✓

---

## Summary

| Evil Implementation | Ruled Out By | Stage |
|---|---|---|
| **Evil 1:** Zero form | `energyForm_one_pos` (E_λ(1) > 0) | Stage 6 (proved) |
| **Evil 2:** Constant form | `energyForm_eq_fourierSymbol_integral` (quadratic scaling) | Stage 5 (axiom) |
| **Evil 3:** L²-norm form | `fourierSymbol_ge_log` (ψ_λ grows logarithmically) | Stage 5 (axiom) |

### Observations

1. **Stage 2 alone is insufficient.** The basic properties (nonnegativity, zero
   at zero) do not distinguish the real form from any of the evil ones. The
   discriminating power comes from Stages 5–6.

2. **Two of three exclusions rely on axioms.** Evil 2 and Evil 3 are only ruled
   out by axiomatized properties (the Fourier representation and Fourier symbol
   lower bound). If those axioms were removed or weakened, the spec would admit
   wrong implementations. This highlights that eliminating those `sorry`-level
   axioms is important for trustworthiness.

3. **The Fourier symbol lower bound is load-bearing.** The axiom
   `fourierSymbol_ge_log` does essential work: it forces the energy form to
   "see" high-frequency behavior, which is what distinguishes the real
   difference-energy form from trivial substitutes like the L² norm.
