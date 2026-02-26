# Stage 4: Markov Property & Null-or-Conull — Completion Report

## Summary

Stage 4 formalized the Markov property and null-or-conull dichotomy for the energy form,
covering Section 5 of `lamportform.tex` (lines 473–782). This stage was implemented across
5 PRs in the `Stage4/` directory.

**Status:** Complete (Issues #40–#44 closed). **0 sorries, 0 axioms.**

## Scope

- **Lemma 5** (Markov property, `lem:markov`): E_λ(Φ∘G) ≤ E_λ(G) for normal contractions
  Φ : ℝ → ℝ satisfying Φ(0) = 0 and |Φ(x) − Φ(y)| ≤ |x − y|. The proof proceeds by
  layered assembly: pointwise nnnorm bounds → lintegral monotonicity → energy integrand →
  total energy inequality.
- **Lemma 6** (null or conull, `lem:null-or-conull`): A translation-invariant measurable
  indicator on an open interval is ae-zero or ae-one. The proof uses mollification to produce
  a continuous translation-invariant function, then Lebesgue differentiation to recover the
  original indicator.

## Files

All files live under `ConnesLean/ConnesLean/Stage4/`:

| File | Description | PR |
|------|-------------|----|
| `NormalContraction.lean` | `IsNormalContraction` structure, `liftReal` ℝ→ℂ bridge, `zeroExtend` factorization | #45 |
| `MarkovProperty.lean` | Pointwise → integral → energy assembly, main Markov theorem | #46 |
| `TranslationInvariance.lean` | `IndicatorTranslationInvariant` structure, `compactMargin`, compact transfer | #47 |
| `MollificationConstancy.lean` | `localAverage`, telescoping constancy, Lebesgue differentiation | #48 |
| `NullOrConull.lean` | Ioo exhaustion by Icc, compact null-or-conull, main Lemma 6 | #49 |

## PRs (in merge order)

| PR | Title | Issue |
|----|-------|-------|
| #45 | Add NormalContraction.lean | #40 |
| #46 | Add MarkovProperty.lean | #41 |
| #47 | Add TranslationInvariance.lean | #42 |
| #48 | Add MollificationConstancy.lean | #43 |
| #49 | Add NullOrConull.lean | #44 |

## Key design decisions

1. **Layered proof structure in MarkovProperty**: The Markov inequality is assembled in four
   layers — pointwise nnnorm bound on |Φ(G(x+t)) − Φ(G(x))| ≤ |G(x+t) − G(x)|, then
   lintegral monotonicity, then the energy integrand (weighted by w(t) or prime coefficients),
   then the total energy inequality. This mirrors the LaTeX proof's logical structure.

2. **IndicatorTranslationInvariant as a structure**: Bundles measurability, support
   containment, and ae-shift hypotheses into a single structure, making the null-or-conull
   proof's hypotheses clean and reusable.

3. **Nat.floor-based step counting for localAverage**: The telescoping constancy argument
   uses `Nat.floor` to count how many translation steps fit in an interval, converting the
   continuous translation-invariance into a finite sum argument.

4. **Lebesgue differentiation via Mathlib's IsUnifLocDoublingMeasure**: The final step
   recovering the indicator from its mollification uses Mathlib's Lebesgue differentiation
   theorem, which requires `IsUnifLocDoublingMeasure` — satisfied by volume on ℝ. This
   required a `maxHeartbeats` bump due to the typeclass search depth.

5. **Real→Complex bridge via liftReal + nnnorm_liftReal_sub**: The `liftReal` function
   embeds ℝ → ℝ contractions into ℂ → ℂ while preserving the nnnorm contraction property,
   enabling seamless transfer between the real-valued Markov argument and the complex-valued
   energy form.

## Deferred work

None. Stage 4 is fully proved with no axioms or sorries.

## Dependencies

- **Blocked by:** Stage 3 (EnergyForm — provides E_λ definition and properties)
- **Blocks:** Stage 6 (irreducibility — uses Lemma 6's null-or-conull conclusion)

## Verification

- `lake build ConnesLean` compiles without errors
- `grep -rn sorry ConnesLean/ConnesLean/Stage4/` returns no results
- `grep -rn "^axiom" ConnesLean/ConnesLean/Stage4/` returns no results
- CI sorry regression check passes on all merged PRs
