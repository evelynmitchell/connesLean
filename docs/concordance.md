# Paper–Code Concordance

Bidirectional map between the LaTeX paper (`lamportform.tex`) and the Lean
formalization (`ConnesLean/`). Use this to navigate from a paper result to
the Lean proof, or from a Lean theorem back to the paper.

Status legend: **proved** = fully proved in Lean, **axiom** = declared as
`axiom` (trusted, not machine-checked), **not yet** = paper section not
formalized.

---

## By paper section

### Section 1 — Setup on R₊\* (lines 95–193)

| Paper result | Lines | Lean file | Lean name | Status |
|---|---|---|---|---|
| Multiplicative Haar measure d\*x | 98–101 | `Stage1/MultiplicativeHaar.lean` | `haarMult` | proved |
| RPos type (ℝ₊\*) | — | `Stage1/MultiplicativeHaar.lean` | `RPos` | proved |
| exp/log coordinate maps | — | `Stage1/MultiplicativeHaar.lean` | `expToRPos`, `logFromRPos` | proved |
| Haar measure invariance | — | `Stage1/MultiplicativeHaar.lean` | `haarMult_mul_invariant` | proved |
| Multiplicative convolution (g\*h) | 102–105 | `Stage1/Convolution.lean` | `mulConv` | proved |
| Involution g\* | 106–109 | `Stage1/Convolution.lean` | `mulInvol` | proved |
| Dilation operator U_a | 110–114, eq.(1) | `Stage1/DilationOperator.lean` | `dilationOp` | proved |
| U_1 = id | — | `Stage1/DilationOperator.lean` | `dilationOp_one` | proved |
| U_{a⁻¹} ∘ U_a = id | — | `Stage1/DilationOperator.lean` | `dilationOp_inv` | proved |
| ‖U_a g‖ = ‖g‖ (L² isometry) | 115–119 | `Stage1/DilationOperator.lean` | `dilationOp_norm_eq` | proved |
| Lemma 1: Convolution inner-product | 122–164 | `Stage1/ConvolutionInnerProduct.lean` | `convolution_eq_inner`, `convolution_at_one` | proved |
| Lemma 2: Unitary identity | 166–191 | `Stage1/UnitaryIdentity.lean` | `unitary_identity`, `unitary_identity_id` | proved |

### Section 2 — Local explicit-formula terms (lines 194–235)

| Paper result | Lines | Lean file | Lean name | Status |
|---|---|---|---|---|
| Prime terms (§2.1) | 206–212 | `Stage2/PrimeDistribution.lean` | `primeFinset`, `primeConstant`, `primeEnergyTerm` | proved |
| Archimedean weight w(t) (§2.2) | 213–235 | `Stage2/ArchimedeanWeight.lean` | `archWeight` | proved |
| Archimedean distribution | — | `Stage2/ArchimedeanDistribution.lean` | `archDistribution` | proved |

### Section 3 — Logarithmic coordinates and translations (lines 236–251)

| Paper result | Lines | Lean file | Lean name | Status |
|---|---|---|---|---|
| Translation operator S_t | 236–251 | `Stage2/TranslationOperator.lean` | `translationOp` | proved |
| S_0 = id | — | `Stage2/TranslationOperator.lean` | `translationOp_zero` | proved |
| S_s ∘ S_t = S_{s+t} | — | `Stage2/TranslationOperator.lean` | `translationOp_add` | proved |
| U_{exp(t)} ∘ exp = S_t ∘ exp | — | `Stage2/TranslationOperator.lean` | `dilation_eq_translation` | proved |
| ‖S_t φ‖ = ‖φ‖ | — | `Stage2/TranslationOperator.lean` | `translationOp_lintegral_norm_eq` | proved |
| Strong continuity of t ↦ ‖φ − S_t φ‖² | — | `Stage2/TranslationOperator.lean` | `translation_norm_sq_continuous` | **axiom** |
| Log-interval I = (−L, L) | — | `Stage2/LogCoordinates.lean` | `logInterval` | proved |
| Zero-extension to I | — | `Stage2/LogCoordinates.lean` | `zeroExtend` | proved |
| L² norm transfer (RPos ↔ ℝ) | — | `Stage2/LogCoordinates.lean` | `lintegral_norm_rpos_eq_real` | proved |

### Section 4 — Energy decomposition (lines 252–471)

| Paper result | Lines | Lean file | Lean name | Status |
|---|---|---|---|---|
| Lemma 3: Prime difference energy | 256–323 | `Stage2/PrimeDistribution.lean` | `primeEnergyTerm`, `totalPrimeEnergy` | proved |
| Lemma 4: Arch difference energy | 326–431 | `Stage2/ArchimedeanWeight.lean` | `archEnergyIntegrand`, `archEnergyIntegral` | proved |
| Shifted intervals disjoint | — | `Stage2/SupportDisjointness.lean` | `Ioo_disjoint_shift` | proved |
| Orthogonality for large shifts | — | `Stage2/SupportDisjointness.lean` | `pointwise_mul_zero_of_large_shift` | proved |
| Definition 3.1: Energy form E_λ(G) | 435–470 | `Stage2/EnergyForm.lean` | `energyForm` | proved |
| E_λ(G) ≥ 0 | — | `Stage2/EnergyForm.lean` | `energyForm_nonneg` | proved |
| E_λ(0) = 0 | — | `Stage2/EnergyForm.lean` | `energyForm_zero` | proved |
| Total correction ≤ 0 | — | `Stage2/EnergyForm.lean` | `totalCorrection_prime_nonpos` | proved |

### Section 5 — Markov property (lines 473–538)

| Paper result | Lines | Lean file | Lean name | Status |
|---|---|---|---|---|
| Definition: Normal contraction | 476–479 | `Stage4/NormalContraction.lean` | `IsNormalContraction` | proved |
| abs is a normal contraction | — | `Stage4/NormalContraction.lean` | `isNormalContraction_abs` | proved |
| id is a normal contraction | — | `Stage4/NormalContraction.lean` | `isNormalContraction_id` | proved |
| Indicator–contraction commutation | — | `Stage4/NormalContraction.lean` | `indicator_comp_normalContraction` | proved |
| Lemma 5: Markov property | 481–537 | `Stage4/MarkovProperty.lean` | `energyForm_comp_normalContraction_le` | proved |
| Corollary: E_λ(\|G\|) ≤ E_λ(G) | — | `Stage4/MarkovProperty.lean` | `energyForm_abs_le` | proved |

### Section 6 — Translation-invariance lemma (lines 539–641)

| Paper result | Lines | Lean file | Lean name | Status |
|---|---|---|---|---|
| IndicatorTranslationInvariant | 542 | `Stage4/TranslationInvariance.lean` | `IndicatorTranslationInvariant` | proved |
| Compact margin | — | `Stage4/TranslationInvariance.lean` | `compactMargin`, `compactMargin_pos` | proved |
| ae shift on compact subintervals | — | `Stage4/TranslationInvariance.lean` | `indicator_ae_shift_on_compact` | proved |
| Local average | — | `Stage4/MollificationConstancy.lean` | `localAverage` | proved |
| Lebesgue differentiation | — | `Stage4/MollificationConstancy.lean` | `localAverage_tendsto_ae` | proved |
| Local average constancy | — | `Stage4/MollificationConstancy.lean` | `localAverage_const_on_compact` | proved |
| Ioo covered by Icc unions | — | `Stage4/NullOrConull.lean` | `ioo_subset_iUnion_icc` | proved |
| Lemma 6: Null or conull | 542–641 | `Stage4/NullOrConull.lean` | `null_or_conull_of_translation_invariant` | proved |

### Section 7.1 — Indicator energy criterion (lines 645–725)

| Paper result | Lines | Lean file | Lean name | Status |
|---|---|---|---|---|
| Arch energy = 0 extraction | — | `Stage6/IndicatorEnergy.lean` | `archEnergy_eq_zero_of_energyForm_eq_zero` | proved |
| Prime energy = 0 extraction | — | `Stage6/IndicatorEnergy.lean` | `primeEnergy_eq_zero_of_energyForm_eq_zero` | proved |
| Continuous ae-zero → pointwise zero | — | `Stage6/IndicatorEnergy.lean` | `continuous_ae_zero_imp_zero` | proved |
| L² zero → ae equal | — | `Stage6/IndicatorEnergy.lean` | `ae_eq_of_lintegral_nnnorm_rpow_zero` | proved |
| Lemma 7: E_λ(1_B) = 0 ⟹ null or conull | 647–696 | `Stage6/IndicatorEnergy.lean` | `energyForm_indicator_null_or_conull` | proved |

### Section 7.2 — Operator realization (lines 726–1209)

| Paper result | Lines | Lean file | Lean name | Status |
|---|---|---|---|---|
| Fourier symbol ψ_λ(ξ) | 783–797 | `Stage5/FourierSymbol.lean` | `fourierSymbol` | proved |
| Arch Fourier symbol | 790 | `Stage5/FourierSymbol.lean` | `archFourierSymbol` | proved |
| Prime Fourier symbol | 793 | `Stage5/FourierSymbol.lean` | `primeFourierSymbol` | proved |
| ψ_λ ≥ 0 | — | `Stage5/FourierSymbol.lean` | `fourierSymbol_nonneg` | proved |
| ψ_λ even | — | `Stage5/FourierSymbol.lean` | `fourierSymbol_even` | proved |
| ψ_λ(0) = 0 | — | `Stage5/FourierSymbol.lean` | `fourierSymbol_zero` | proved |
| Lemma 9: Fourier representation | 783–842 | `Stage5/ClosedForm.lean` | `energyForm_eq_fourierSymbol_integral` | **axiom** |
| Form domain D(E_λ) | — | `Stage5/ClosedForm.lean` | `formDomain` | proved |
| Domain = weighted Fourier space | — | `Stage5/ClosedForm.lean` | `formDomain_eq_weighted_fourier` | **axiom** |
| Proposition 6: Closed form on L²(ℝ) | 844–900 | `Stage5/ClosedForm.lean` | `energyForm_closed_on_line` | **axiom** |
| Proposition 7: Closed form on L²(I) | 901–936 | `Stage5/ClosedForm.lean` | `energyForm_closed_on_interval` | **axiom** |
| Lemma 10: w(t) ≥ 1/(2t) | 940–962 | `Stage5/SymbolLowerBound.lean` | `archWeight_ge_inv_two_t` | proved |
| Lemma 11: ψ_λ ≥ c₁ log\|ξ\| − c₂ | 964–1021 | `Stage5/SymbolLowerBound.lean` | `fourierSymbol_ge_log` | **axiom** |
| Corollary 12: Frequency moment | 1023–1057 | `Stage5/SymbolLowerBound.lean` | `frequency_moment_control` | **axiom** |
| ψ_λ → +∞ | — | `Stage5/SymbolLowerBound.lean` | `fourierSymbol_tendsto_atTop` | proved (from axiom #6) |
| Theorem KR: Kolmogorov–Riesz | 1061–1076 | `Stage5/CompactEmbedding.lean` | `kolmogorov_riesz_compact` | **axiom** |
| Form-norm ball | — | `Stage5/CompactEmbedding.lean` | `formNormBall` | proved |
| Lemma 13: Translation equicontinuity | 1078–1127 | `Stage5/CompactEmbedding.lean` | `formNormBall_equicontinuous` | **axiom** |
| Proposition 8: Compact embedding | 1129–1157 | `Stage5/CompactEmbedding.lean` | `formNormBall_isRelativelyCompactL2` | proved (from axioms) |
| KatoOperator structure | — | `Stage5/CompactResolvent.lean` | `KatoOperator` | proved |
| Kato representation theorem | 1164–1174 | `Stage5/CompactResolvent.lean` | `kato_operator` | **axiom** |
| Theorem 9: Compact resolvent | 1159–1209 | `Stage5/CompactResolvent.lean` | `compact_resolvent_of_compact_embedding` | proved (from axioms) |

### Section 7.3 — Semigroup and irreducibility (lines 1212–1461)

| Paper result | Lines | Status |
|---|---|---|
| Definition: Irreducibility for semigroups | 1215–1218 | **not yet** |
| Lemma 14: Invariant ideals split the form | 1220–1310 | **not yet** |
| Proposition 9: Triviality of invariant ideals | 1312–1440 | **not yet** |
| Corollary 13: Irreducibility for E_λ | 1442–1461 | **not yet** |

### Section 8 — Positivity improving and ground state (lines 1463–1558)

| Paper result | Lines | Status |
|---|---|---|
| External: Positivity improving theorem | 1469–1478 | **not yet** |
| External: Simplicity of principal eigenvalue | 1480–1499 | **not yet** |
| Proposition 10: Ground state for A_λ | 1503–1557 | **not yet** |

### Section 9 — Evenness of the ground state (lines 1559–1676)

| Paper result | Lines | Status |
|---|---|---|
| Proposition 11: Inversion symmetry | 1562–1637 | **not yet** |
| Corollary 14: Even ground state | 1639–1676 | **not yet** |

---

## By Lean file

| Lean file | Paper section(s) | Key results |
|---|---|---|
| `Stage1/MultiplicativeHaar.lean` | §1 | `RPos`, `haarMult`, `expToRPos`, coordinate maps |
| `Stage1/DilationOperator.lean` | §1 eq.(1) | `dilationOp`, isometry, group law |
| `Stage1/Convolution.lean` | §1 | `mulConv`, `mulInvol`, involutivity |
| `Stage1/ConvolutionInnerProduct.lean` | §1 Lemma 1 | `convolution_eq_inner`, `convolution_at_one` |
| `Stage1/UnitaryIdentity.lean` | §1 Lemma 2 | `unitary_identity` |
| `Stage2/TranslationOperator.lean` | §3 | `translationOp`, L² isometry, strong continuity (**axiom**) |
| `Stage2/LogCoordinates.lean` | §3 | `logInterval`, `zeroExtend`, norm transfer |
| `Stage2/SupportDisjointness.lean` | §4 | Disjoint supports, orthogonality |
| `Stage2/PrimeDistribution.lean` | §2.1, §4 Lemma 3 | `primeFinset`, `primeEnergyTerm` |
| `Stage2/ArchimedeanWeight.lean` | §2.2, §4 Lemma 4 | `archWeight`, bounds, integrability |
| `Stage2/ArchimedeanDistribution.lean` | §2.2 | `archDistribution` |
| `Stage2/EnergyForm.lean` | §4 Def 3.1 | `energyForm`, nonnegativity |
| `Stage4/NormalContraction.lean` | §5 Def | `IsNormalContraction`, `liftReal`, norm bridge |
| `Stage4/MarkovProperty.lean` | §5 Lemma 5 | `energyForm_comp_normalContraction_le` |
| `Stage4/TranslationInvariance.lean` | §6 | `IndicatorTranslationInvariant`, compact margin |
| `Stage4/MollificationConstancy.lean` | §6 | `localAverage`, Lebesgue differentiation |
| `Stage4/NullOrConull.lean` | §6 Lemma 6 | `null_or_conull_of_translation_invariant` |
| `Stage5/FourierSymbol.lean` | §7.2 Lemma 9 | `fourierSymbol`, nonnegativity, evenness |
| `Stage5/SymbolLowerBound.lean` | §7.2 Lemmas 10–11, Cor 12 | Weight bound, log growth (**2 axioms**) |
| `Stage5/ClosedForm.lean` | §7.2 Props 6–7 | `formDomain`, `IsClosedEnergyForm` (**4 axioms**) |
| `Stage5/CompactEmbedding.lean` | §7.2 Thm KR, Lemma 13, Prop 8 | `formNormBall`, compactness (**2 axioms**) |
| `Stage5/CompactResolvent.lean` | §7.2 Thm 9 | `KatoOperator`, compact resolvent (**1 axiom**) |
| `Stage6/IndicatorEnergy.lean` | §7.1 Lemma 7 | `energyForm_indicator_null_or_conull` |

---

## Axiom summary

| # | Axiom | Paper reference | Lean location |
|---|---|---|---|
| 1 | `translation_norm_sq_continuous` | Engel-Nagel I.5.8 | `Stage2/TranslationOperator.lean:97` |
| 2 | `energyForm_eq_fourierSymbol_integral` | Lemma 9 (lines 844–872) | `Stage5/ClosedForm.lean:77` |
| 3 | `formDomain_eq_weighted_fourier` | Prop 6 Step 2 | `Stage5/ClosedForm.lean:93` |
| 4 | `energyForm_closed_on_line` | Prop 6 (lines 874–907) | `Stage5/ClosedForm.lean:116` |
| 5 | `energyForm_closed_on_interval` | Prop 7 (lines 909–936) | `Stage5/ClosedForm.lean:133` |
| 6 | `fourierSymbol_ge_log` | Lemma 11 (lines 964–1021) | `Stage5/SymbolLowerBound.lean:146` |
| 7 | `frequency_moment_control` | Cor 12 (lines 1023–1057) | `Stage5/SymbolLowerBound.lean:163` |
| 8 | `kolmogorov_riesz_compact` | Thm KR (lines 1061–1076) | `Stage5/CompactEmbedding.lean:58` |
| 9 | `formNormBall_equicontinuous` | Lemma 13 (lines 1078–1127) | `Stage5/CompactEmbedding.lean:71` |
| 10 | `kato_operator` | Thm 9 Step 1 (lines 1164–1174) | `Stage5/CompactResolvent.lean:69` |
