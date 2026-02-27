# Notation Glossary

Paper notation → Lean name, with links to source definitions.

## Types and spaces

| Paper | Lean | Defined in |
|---|---|---|
| ℝ₊\* = (0, ∞) | `RPos` | [`Stage1/MultiplicativeHaar.lean:30`](../ConnesLean/ConnesLean/Stage1/MultiplicativeHaar.lean) |
| d\*x = dx/x | `haarMult` | [`Stage1/MultiplicativeHaar.lean:117`](../ConnesLean/ConnesLean/Stage1/MultiplicativeHaar.lean) |
| I = (−log λ, log λ) | `logInterval L` | [`Stage2/LogCoordinates.lean:32`](../ConnesLean/ConnesLean/Stage2/LogCoordinates.lean) |
| D(E_λ) (form domain) | `formDomain Λ` | [`Stage5/ClosedForm.lean:38`](../ConnesLean/ConnesLean/Stage5/ClosedForm.lean) |
| B(M) (form-norm ball) | `formNormBall Λ M` | [`Stage5/CompactEmbedding.lean:45`](../ConnesLean/ConnesLean/Stage5/CompactEmbedding.lean) |

## Operators

| Paper | Lean | Defined in |
|---|---|---|
| U_a g (dilation) | `dilationOp a g` | [`Stage1/DilationOperator.lean:35`](../ConnesLean/ConnesLean/Stage1/DilationOperator.lean) |
| S_t φ (translation) | `translationOp t φ` | [`Stage2/TranslationOperator.lean:36`](../ConnesLean/ConnesLean/Stage2/TranslationOperator.lean) |
| g \* h (convolution) | `mulConv g h` | [`Stage1/Convolution.lean:34`](../ConnesLean/ConnesLean/Stage1/Convolution.lean) |
| g\* (involution) | `mulInvol g` | [`Stage1/Convolution.lean:40`](../ConnesLean/ConnesLean/Stage1/Convolution.lean) |
| (A_λ + I)⁻¹ (resolvent) | `KatoOperator.resolvent` | [`Stage5/CompactResolvent.lean:43`](../ConnesLean/ConnesLean/Stage5/CompactResolvent.lean) |

## Coordinate maps

| Paper | Lean | Defined in |
|---|---|---|
| exp : ℝ → ℝ₊\* | `expToRPos u` | [`Stage1/MultiplicativeHaar.lean:72`](../ConnesLean/ConnesLean/Stage1/MultiplicativeHaar.lean) |
| log : ℝ₊\* → ℝ | `logFromRPos x` | [`Stage1/MultiplicativeHaar.lean:75`](../ConnesLean/ConnesLean/Stage1/MultiplicativeHaar.lean) |
| G̃(u) = G(u) · 1_I(u) | `zeroExtend G I` | [`Stage2/LogCoordinates.lean:36`](../ConnesLean/ConnesLean/Stage2/LogCoordinates.lean) |
| cast ℝ → ℂ | `liftReal G` | [`Stage4/NormalContraction.lean:78`](../ConnesLean/ConnesLean/Stage4/NormalContraction.lean) |

## Energy form and components

| Paper | Lean | Defined in |
|---|---|---|
| E_λ(G) | `energyForm Λ G` | [`Stage2/EnergyForm.lean:46`](../ConnesLean/ConnesLean/Stage2/EnergyForm.lean) |
| w(t) = e^{t/2} / (2 sinh t) | `archWeight t` | [`Stage2/ArchimedeanWeight.lean:44`](../ConnesLean/ConnesLean/Stage2/ArchimedeanWeight.lean) |
| Archimedean energy integrand | `archEnergyIntegrand G L t` | [`Stage2/ArchimedeanWeight.lean:207`](../ConnesLean/ConnesLean/Stage2/ArchimedeanWeight.lean) |
| Archimedean energy integral | `archEnergyIntegral G L` | [`Stage2/ArchimedeanWeight.lean:215`](../ConnesLean/ConnesLean/Stage2/ArchimedeanWeight.lean) |
| Prime energy term (single p, m) | `primeEnergyTerm p m G L` | [`Stage2/PrimeDistribution.lean:80`](../ConnesLean/ConnesLean/Stage2/PrimeDistribution.lean) |
| Total prime energy (sum over m) | `totalPrimeEnergy p Λ G L` | [`Stage2/PrimeDistribution.lean:88`](../ConnesLean/ConnesLean/Stage2/PrimeDistribution.lean) |
| c_p(λ) (prime constant) | `primeConstant p Λ` | [`Stage2/PrimeDistribution.lean:56`](../ConnesLean/ConnesLean/Stage2/PrimeDistribution.lean) |
| Archimedean distribution σ_∞ | `archDistribution f` | [`Stage2/ArchimedeanDistribution.lean:45`](../ConnesLean/ConnesLean/Stage2/ArchimedeanDistribution.lean) |

## Fourier analysis

| Paper | Lean | Defined in |
|---|---|---|
| ψ_λ(ξ) (Fourier symbol) | `fourierSymbol Λ ξ` | [`Stage5/FourierSymbol.lean:55`](../ConnesLean/ConnesLean/Stage5/FourierSymbol.lean) |
| ψ_λ^arch(ξ) | `archFourierSymbol L ξ` | [`Stage5/FourierSymbol.lean:39`](../ConnesLean/ConnesLean/Stage5/FourierSymbol.lean) |
| ψ_λ^prime(ξ) | `primeFourierSymbol Λ ξ` | [`Stage5/FourierSymbol.lean:46`](../ConnesLean/ConnesLean/Stage5/FourierSymbol.lean) |
| Ĝ(ξ) (Fourier transform) | `FourierTransform.fourier G ξ` | Mathlib |

## Structures and predicates

| Paper | Lean | Defined in |
|---|---|---|
| Φ is a normal contraction | `IsNormalContraction Φ` | [`Stage4/NormalContraction.lean:31`](../ConnesLean/ConnesLean/Stage4/NormalContraction.lean) |
| 1_B shift-invariant on I | `IndicatorTranslationInvariant B I ε` | [`Stage4/TranslationInvariance.lean:37`](../ConnesLean/ConnesLean/Stage4/TranslationInvariance.lean) |
| E_λ is a closed form | `IsClosedEnergyForm Λ` | [`Stage5/ClosedForm.lean:52`](../ConnesLean/ConnesLean/Stage5/ClosedForm.lean) |
| K is relatively compact in L² | `IsRelativelyCompactL2 K` | [`Stage5/CompactEmbedding.lean:32`](../ConnesLean/ConnesLean/Stage5/CompactEmbedding.lean) |
| A_λ has compact resolvent | `HasCompactResolvent Λ T` | [`Stage5/CompactResolvent.lean:83`](../ConnesLean/ConnesLean/Stage5/CompactResolvent.lean) |

## Combinatorial parameters

| Paper | Lean | Defined in |
|---|---|---|
| λ (cutoff parameter, λ > 1) | `cutoffLambda` or `Λ` | throughout |
| L = log λ | `Real.log cutoffLambda` | throughout |
| {p prime : p ≤ λ²} | `primeFinset Λ` | [`Stage2/PrimeDistribution.lean:40`](../ConnesLean/ConnesLean/Stage2/PrimeDistribution.lean) |
| {m : p^m ≤ λ²} | `exponentFinset p Λ` | [`Stage2/PrimeDistribution.lean:44`](../ConnesLean/ConnesLean/Stage2/PrimeDistribution.lean) |
| ⌊λ²⌋ | `primeBound Λ` | [`Stage2/PrimeDistribution.lean:31`](../ConnesLean/ConnesLean/Stage2/PrimeDistribution.lean) |

## Auxiliary analysis

| Paper | Lean | Defined in |
|---|---|---|
| Local average (mollification) | `localAverage f η u` | [`Stage4/MollificationConstancy.lean:46`](../ConnesLean/ConnesLean/Stage4/MollificationConstancy.lean) |
| Compact margin δ | `compactMargin α β a b` | [`Stage4/TranslationInvariance.lean:50`](../ConnesLean/ConnesLean/Stage4/TranslationInvariance.lean) |
