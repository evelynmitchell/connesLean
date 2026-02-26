# Stage 5: Fourier Analysis & Compact Resolvent — Completion Report

## Summary

Stage 5 formalized the Fourier-analytic infrastructure and compact resolvent theorem,
covering Sections 7.2–7.4 of `lamportform.tex` (lines 783–1209). This stage was implemented
across 5 PRs in the `Stage5/` directory.

**Status:** Complete (Issues #50–#54 closed). **0 sorries, 9 axioms** (deep functional
analysis results not yet available in Mathlib).

## Scope

- **Lemma 9** (Fourier symbol ψ_λ): Definition as sum of archimedean and prime parts,
  with nonnegativity, evenness, and zero-at-origin properties.
- **Lemmas 10–11, Corollary 12** (symbol lower bounds): w(t) ≥ 1/(2t) bound,
  logarithmic growth ψ_λ(ξ) ≥ C·log(1+|ξ|) (axiom), and tendsto ∞.
- **Propositions 6–7** (closed energy form): formDomain as ENNReal finiteness set,
  IsClosedEnergyForm structure, Fourier representation of E_λ (axioms).
- **Theorem KR, Lemma 13, Proposition 8** (compact embedding): Kolmogorov-Riesz
  criterion (axiom), equicontinuity of formNormBall (axiom), compact embedding.
- **Theorem 9** (compact resolvent): KatoOperator structure, Kato representation
  theorem (axiom), compact resolvent via form identity → formNormBall → compact embedding.

## Files

All files live under `ConnesLean/ConnesLean/Stage5/`:

| File | Description | PR |
|------|-------------|----|
| `FourierSymbol.lean` | ψ_λ = archFourierSymbol + primeFourierSymbol, nonneg/even/zero properties | #55 |
| `SymbolLowerBound.lean` | w(t) ≥ 1/(2t), log growth (axiom), tendsto ∞ | #56 |
| `ClosedForm.lean` | formDomain, IsClosedEnergyForm, Fourier representation (axioms) | #57 |
| `CompactEmbedding.lean` | formNormBall, KR criterion (axiom), equicontinuity (axiom), compact embedding | #58 |
| `CompactResolvent.lean` | KatoOperator structure, Kato theorem (axiom), compact resolvent | #60 |

## PRs (in merge order)

| PR | Title | Issue |
|----|-------|-------|
| #55 | Add FourierSymbol.lean | #50 |
| #56 | Add SymbolLowerBound.lean | #51 |
| #57 | Add ClosedForm.lean | #52 |
| #58 | Add CompactEmbedding.lean | #53 |
| #60 | Add CompactResolvent.lean | #54 |

## Key design decisions

1. **Fourier symbol as plain ℝ-valued function**: Defined `fourierSymbol` as the sum
   `archFourierSymbol + primeFourierSymbol`, keeping it a plain ℝ → ℝ function rather
   than wrapping it in any operator-theoretic structure. Properties (nonneg, even, zero
   at origin) are proved as separate lemmas.

2. **formDomain as ENNReal finiteness**: Defined as the simple set
   `{G | energyForm Λ G ≠ ⊤}`, avoiding the need for weighted Sobolev space machinery.
   The equivalence with a weighted Fourier space is stated as an axiom for future infilling.

3. **Sequential compactness (IsRelativelyCompactL2)**: Uses sequential compactness
   (every sequence has a convergent subsequence) rather than topological compactness,
   avoiding the need to construct a topology on L² function spaces.

4. **KatoOperator structure**: Encapsulates the resolvent properties (self-adjointness,
   nonnegativity, domain inclusion, form identity) without requiring a full operator theory
   library. The compact resolvent follows by chaining: form identity → norm ball containment
   → compact embedding.

5. **Compact resolvent proved by composition**: The final `resolvent_compact` theorem
   chains three ingredients: the Kato representation gives a form identity, the form identity
   shows the resolvent image lands in formNormBall, and the compact embedding theorem gives
   compactness of formNormBall in L².

## Deferred work (9 axioms to infill)

| Axiom | File | Line | Difficulty | Why axiom |
|-------|------|------|-----------|-----------|
| `fourierSymbol_ge_log` | SymbolLowerBound.lean | 146 | Medium | Oscillatory integral lower bound (Lemma 11); needs Fourier analysis of sin² integrals |
| `frequency_moment_control` | SymbolLowerBound.lean | 163 | Easy | Direct corollary of `fourierSymbol_ge_log`; should be straightforward once that's proved |
| `energyForm_eq_fourierSymbol_integral` | ClosedForm.lean | 77 | Hard | Plancherel theorem + ENNReal↔ℝ bridging at integration boundary |
| `formDomain_eq_weighted_fourier` | ClosedForm.lean | 93 | Hard | Weighted Fourier space characterization; depends on Plancherel bridge |
| `energyForm_closed_on_line` | ClosedForm.lean | 116 | Hard | Kato closed-form theory (graph completeness); not in Mathlib |
| `energyForm_closed_on_interval` | ClosedForm.lean | 133 | Medium | Restriction of L²(ℝ) closedness to L²(I); needs support-propagation argument |
| `kolmogorov_riesz_compact` | CompactEmbedding.lean | 58 | Hard | Kolmogorov-Riesz theorem (Brezis, Cor 4.27); full L² compactness criterion |
| `formNormBall_equicontinuous` | CompactEmbedding.lean | 71 | Medium | Plancherel + frequency splitting into low/high (Lemma 13) |
| `kato_operator` | CompactResolvent.lean | 69 | Hard | Kato representation theorem (Thm VI.2.1); deep functional analysis |

**Priority for infilling:** `frequency_moment_control` (easy, depends on one other) →
`fourierSymbol_ge_log` + `formNormBall_equicontinuous` (medium) → the rest (hard, need
Mathlib gaps filled).

See also `docs/project-kolmogorov-riesz.md` and `docs/project-formNormBall-equicontinuity.md`
for detailed infilling plans on the two CompactEmbedding axioms.

## Dependencies

- **Blocked by:** Stage 3 (EnergyForm — provides E_λ definition and properties)
- **Blocks:** Stage 6 (spectral properties of A_λ, Perron-Frobenius)

## Verification

- `lake build ConnesLean` compiles without errors
- `grep -rn sorry ConnesLean/ConnesLean/Stage5/` returns no results
- `grep -rn "^axiom" ConnesLean/ConnesLean/Stage5/` returns exactly 9 results
- CI sorry regression check passes on all merged PRs
