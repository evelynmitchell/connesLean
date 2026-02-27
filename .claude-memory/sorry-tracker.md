# Outstanding sorry Proofs

## MultiplicativeHaar.lean — DONE (PR #13)
All sorries closed:
- ~~`measurable_expToRPos`~~ — proved via `continuous_exp.measurable.subtype_mk`
- ~~`measurable_logFromRPos`~~ — proved via `continuous_log'.measurable`
- ~~`haarMult_sigmaFinite`~~ — proved via `expEquivRPos.sigmaFinite_map`
- ~~`haarMult_mul_invariant`~~ — proved via conjugation + Lebesgue translation invariance

## DilationOperator.lean — DONE
- ~~`dilationOp_norm_eq`~~ — proved via exp/log conjugation + Lebesgue translation invariance
- ~~`inner_dilationOp_le`~~ — proved via AM-GM + MeasurePreserving change-of-variables + integral_eq_lintegral_of_nonneg_ae

## Convolution.lean — DONE
- ~~`mulConv_mulInvol_integrable`~~ — proved via MeasurePreserving (· / a) + MemLp.star + MemLp.integrable_mul (Hölder)

## ConvolutionInnerProduct.lean — DONE
- ~~`convolution_inv_eq_conj`~~ — proved via integral_conj + MeasurableEquiv change-of-variables + mul_comm
- ~~`convolution_at_one`~~ — proved via RCLike.mul_conj + norm_cast + integral_eq_lintegral_of_nonneg_ae + ENNReal.ofReal_rpow_of_nonneg

## Summary
- **Closed:** 9/9 (MultiplicativeHaar: 4, DilationOperator: 2, Convolution: 1, ConvolutionInnerProduct: 2)
- **Remaining:** 0
