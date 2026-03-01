# Lean & LSpec Patterns

## Finding Mathlib lemmas
- Use Loogle to search by type signature; always check before guessing names
- Use `lean_local_search` to verify a name exists before using it in a proof

## LSpec & noncomputable barrier
- `check'` is compile-time only, produces `TestSeq`; must use `let t : TestSeq := check' "name" (prop)`
- All Stage 1+ definitions are `noncomputable` (depend on Mathlib real analysis)
- `checkIO'` cannot evaluate noncomputable defs — test Nat mirrors instead

## RPos type
- `abbrev RPos := {x : ℝ // 0 < x}` — has One, Mul, Inv, Div, TopologicalSpace, MeasurableSpace
- `ℝ` equality is not `DecidableEq` so LSpec `test` can't check RPos value equalities

## Measurability patterns
- For standard functions on subtypes: `Continuous.measurable` + `.subtype_mk`
- Build `MeasurableEquiv` structures early — they transfer sigma-finiteness, pushforward for free
- Conjugation trick: rewrite RPos multiplication into ℝ translation via exp/log, then use `map_add_left_eq_self`

## norm_cast requires imported lemmas
- `norm_cast` only uses `@[norm_cast]`-tagged lemmas that are **imported**
- Key: `integral_ofReal` (in `Bochner.ContinuousLinearMap`) lets `norm_cast` pull `↑` out of integrals

## MeasurePreserving for RPos division
- Two-field constructor: measurability via `.subtype_mk`, map equality via conjugation + translation invariance
- `MemLp.comp_measurePreserving` transfers L² membership through preserved maps

## Hölder inequality for L² functions
- `MemLp.integrable_mul` : `MemLp f 2 μ → MemLp g 2 μ → Integrable (f * g) μ`
- `MemLp.star` : `MemLp f p μ → MemLp (star f) p μ`

## Integrable dot-notation gotcha
- `Integrable` is a `def` (unfolds to `And`); dot notation may resolve to `And.method`
- Fix: use explicit namespace — `Integrable.congr h_int ...` not `h_int.congr ...`

## lintegral_add_left_eq_self
- Provide `(μ := (volume : Measure ℝ))` explicitly; use `simp_rw [sub_eq_add_neg, add_comm _ (-c)]` for expected form

## Lean 4 parsing quirks
- `let x := e; -body` fails — wrap in parens: `((-x) + y)`
- `set_option maxHeartbeats N in` must appear BEFORE docstring, not between docstring and `theorem`
- `∂volume` in multi-line integrands can fail — omit it (volume is default) or use `let` bindings

## Normal contraction / Lipschitz
- No `Real.lipschitzWith_abs` — use `LipschitzWith.of_dist_le_mul` + `abs_abs_sub_abs_le_abs_sub`
- `Set.indicator_comp_of_zero` composes: apply twice for `Φ` then `(↑· : ℝ → ℂ)`
- `IsCompact.infDist_compl_pos` does NOT exist — use direct arithmetic with `linarith`

## gcongr for weighted ENNReal inequalities
- `gcongr` decomposes `c * ∫ ‖f‖₊^2 ≤ c * ∫ ‖g‖₊^2` into pointwise goals automatically
- Can be expensive — may need `set_option maxHeartbeats 800000`
- **Key**: factor out pointwise nnnorm lemma as named lemma, then `gcongr; exact myLemma _ _`

## ae_restrict_of_ae_restrict_of_subset
- Don't use `apply` — Lean can't infer intermediate set `t`
- Do: `have h_sub : S ⊆ T := ...; exact ae_restrict_of_ae_restrict_of_subset h_sub h_ae`

## Import for `volume` on ℝ
- Need `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` (or transitive import)
- Symptom without it: `failed to synthesize instance MeasureSpace ℝ`

## Mathlib lemma name gotchas (v4.28)
- `div_lt_iff` / `div_le_iff` → use `div_lt_iff₀` / `div_le_iff₀` (with subscript zero)
- `Set.indicator_of_notMem` (not `indicator_of_not_mem`)

## Proving bounds on special functions
- **sinh t ≥ t**: Use `mul_sub_le_image_sub_of_le_deriv` (MVT) with `Real.one_le_cosh`
- **sinh t > exp t / 4 (t ≥ 1)**: `nlinarith` with `sq_nonneg (Real.exp t)`, `Real.exp_pos (-t)`, and `exp t ≥ 2`
- **exp cancellation**: `field_simp` + `rw [← Real.exp_add]; simp` handles most cases

## Integrability proof patterns
- **Domination** (`Integrable.mono'`): For unbounded sets, dominate by known integrable function (e.g. `integrableOn_exp_neg_Ioi`)
- **Bounded-on-finite-measure** (`IntegrableOn.of_bound`): Use `refine` (not `apply`) — `C` is a term argument
- **Parameter-dependent** (`Measurable.lintegral_prod_right`): Show `Measurable (Function.uncurry f)`, then chain `.nnnorm.coe_nnreal_ennreal.pow_const _`

## Name collision prevention
- Before declaring a theorem, use `lean_local_search` to check if the name exists
- Convention: `_apply_zero_fun` for "applying to zero function" vs `_zero` for "zero parameter"

## integral_div and integral_add
- `integral_div`: pulls constant division out of integral
- `integral_add h_f h_g`: splits integral of sum (needs integrability of both)

## Transferring ae properties through translations
- Use `measure_preimage_add_right` + `Filter.mem_of_superset` pattern
- Do NOT use `ae_map_iff` — it requires `MeasurableSet` of the property set

## Interval integral change of variables
- `integral_comp_add_right f d : ∫ x in a..b, f(x+d) = ∫ x in (a+d)..(b+d), f x`
- For `uIoc` membership: `rw [Set.uIoc_of_le (by linarith)]` converts to `Ioc`

## Lebesgue differentiation on ℝ
- `IsUnifLocDoublingMeasure.ae_tendsto_average` gives convergence of ball averages ae
- Instance needs `import Mathlib.MeasureTheory.Measure.Haar.NormedSpace`

## ENNReal patterns
- **`linarith` does NOT work on ENNReal.** Use `exact absurd this (ne_of_gt h_vol_pos)`
- **`ne_of_gt`**: `a < b → b ≠ a` (so `ne_of_gt (0 < volume S)` gives `volume S ≠ 0`)
- **`measure_mono_null`** (`s ⊆ t → μ t = 0 → μ s = 0`): pre-prove subset as `have h_sub`
- **Degenerate Icc**: `volume (Icc a b) = 0` when `b ≤ a` — `simp only [Real.volume_Icc]; exact ENNReal.ofReal_of_nonpos (by linarith)`
- **`WithTop.add_top`** (not `ENNReal.add_top`): `x + ⊤ = ⊤`
- **`ne_top_of_le_ne_top hE le_self_add`**: show summand finite when sum is finite
- **`nlinarith` needs division pre-digested**: extract via `rwa [div_lt_iff₀' ...] at hN` first

## simp only vs unfold for definitions with `let`
- `simp only [defName]` > `unfold defName` — simp beta/zeta-reduces `let` bindings
- `unfold` may leave un-reduced `have L := ...` in the goal

## setLIntegral naming
- `setLIntegral_congr_fun`: changes the **integrand** (needs `MeasurableSet s` + `EqOn f g s`)
- `setLIntegral_congr`: changes the **set** (needs `s =ᶠ[ae μ] t`)

## setIntegral_congr_fun and beta-reduction
- Name is `setIntegral_congr_fun` (NOT `setIntegral_congr`) for pointwise equality
- After applying, must `simp only` to beta-reduce lambdas before `rw` can find patterns

## Division/inversion algebra in inequalities
- Don't chain `rw` through `inv_le_comm₀`, `div_le_iff₀` — use `field_simp; ring` to polynomial form, then `nlinarith`
- Feed `nlinarith` strategic squares: `sq_nonneg x`, `sq_nonneg (x - c)`

## Hyperbolic function names
- `Real.continuous_cosh` / `Real.continuous_sinh` (NOT `continuousOn_` variants)
- `Real.one_le_exp` (for `0 ≤ x → 1 ≤ exp x`); `Real.exp_add` for `exp(a) * exp(b) = exp(a+b)`

## monotoneOn_of_deriv_nonneg
- Args: `(convex D) (cont_on D) (diff_on interior_D) (deriv_nonneg interior_D)`
- `interior_Icc` converts membership to `Ioo`; `HasDerivAt.deriv` rewrites `deriv f x`

## Set vs Finset namespace ambiguity
- Opening both causes ambiguity for `mem_Ioo`, `preimage`, `Ioo` — qualify with `Set.` prefix

## ENNReal indicator elaboration
- `≤ᵐ[μ]` must be on one line — parser doesn't handle line breaks between `≤ᵐ` and `[μ]`
- `.indicator` on new line resolves wrong with `open Real` — keep on same line as closing paren
- `Set.indicator_of_notMem` takes explicit function argument: `indicator_of_notMem h_nmem (1 : ℝ → ENNReal)`
- Bounding `∫⁻ ‖φ(u) - φ(u-t)‖₊²`: use `(I ∪ (· - t) ⁻¹' I).indicator 1` (covers all 4 cases)

## lintegral_indicator_one for bounded-set finiteness
- `lintegral_indicator_one`: `MeasurableSet s → ∫⁻ a, s.indicator 1 a ∂μ = μ s`
- `logInterval` uses `Ioo` — use `measure_Ioo_lt_top` for finiteness

## Axiom design
- Weakest hypotheses needed (closest to actual theorem) — opposite to theorems where stronger conclusions are better
- Every axiom needs a `**Soundness:**` annotation (enforced by `scripts/lint_axiom_soundness.sh`)

## ENNReal: proving a + b ≤ 0 forces both zero
- `∫⁻ u, ‖(0 : ℝ → ℂ) u‖₊ ^ (2 : ℝ)` does NOT simplify to 0 via the usual simp lemmas
- Fix: `have h_rhs : (∫⁻ u, ‖(0 : ℝ → ℂ) u‖₊ ^ (2 : ℝ)) = 0 := by simp` then `rw [h_rhs] at h`
- For `a + b ≤ 0` in ENNReal: `le_antisymm (le_trans le_self_add h) (zero_le _)` gives `a = 0`
- For the other summand: `le_antisymm (le_trans le_add_self h) (zero_le _)` gives `b = 0`

## Nat.floor for telescoping
- `Nat.floor_le (h : 0 ≤ x) : ↑⌊x⌋₊ ≤ x`; `Nat.lt_floor_add_one x : x < ↑⌊x⌋₊ + 1`

## `show` vs `change` linter
- `show` is now linted — use `change` when modifying the goal (e.g., unfolding definitions)
- `show` is fine only when it matches the current goal exactly (documentation)

## `rw` with complex set expressions
- When target involves lambdas/preimages, `rw` often fails — use `set B' := ...` + `have h_eq`
- For ENNReal coercions: `↑(x.toNNReal) = ENNReal.ofReal x` holds by `rfl`, so `change` can switch

## ENNReal rpow patterns
- **`simp` handles {0,1} ENNReal rpow automatically**: For indicator case analysis where values are in {0,1}, `simp` with indicator membership lemmas closes goals without needing explicit `rpow_two_zero`/`rpow_two_one` helpers. The rpow helpers are still useful for `simp only` or manual `rw` chains.
- **Pre-compute rpow facts** (when `simp` can't reach): `h_zero_rpow : (0:ENNReal) ^ (2:ℝ) = 0 := ENNReal.zero_rpow_of_pos ...` and `h_one_rpow : (1:ENNReal) ^ (2:ℝ) = 1 := ENNReal.one_rpow _`.
- **`ENNReal.rpow_eq_zero_iff`** (bidirectional): `x ^ y = 0 ↔ (x = 0 ∧ 0 < y) ∨ (x = ⊤ ∧ y < 0)`. Use this instead of constructing positivity proofs for rpow. `norm_num` dispatches the impossible ⊤ branch.
- **`ENNReal.rpow_le_rpow`**: `a ≤ b → 0 ≤ r → a ^ r ≤ b ^ r`. Useful for monotone bounds.
- **Always use `NNReal` / `ENNReal`** in type signatures, never `ℝ≥0` / `ℝ≥0∞`. The notation is 3 tokens (`ℝ`, `≥`, `0`) and will misparse without the right `open scoped`. The spelled-out name is unambiguous.

## Pi.zero_apply for ae filter
- `f =ᶠ[ae μ] 0` unfolds to `∀ᵐ x ∂μ, f x = (0 : α → β) x`, NOT `f x = 0`
- After `filter_upwards [h_ae] with u hu`, always do `simp only [Pi.zero_apply] at hu` to get `f u = 0`

## Measurable.indicator argument order
- `Measurable.indicator` takes `(hf : Measurable f) (hs : MeasurableSet s)` — dot notation on `Measurable`
- `measurable_const.indicator hB_meas` ✓ (NOT `hB_meas.indicator measurable_const`)

## lintegral_eq_zero_iff with restricted measures
- `lintegral_eq_zero_iff (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0`
- Works with any measure including `volume.restrict S` — no `.restrict` suffix needed on measurability

## ae-equality through measure-preserving translations
- `h_ae.comp_tendsto (measurePreserving_sub_const t).quasiMeasurePreserving.tendsto_ae`
- Gives: if `φ =ᵐ[volume] ψ` then `(fun u => φ (u - t)) =ᵐ[volume] (fun u => ψ (u - t))`
- Reusable for propagating ae-equality through energy form integrands

## Restricted lintegral positivity
- `lintegral_pos_iff_support h_meas` works on restricted measure (set integral form)
- To show `0 < (volume.restrict S)(support f)`, use:
  `Measure.le_restrict_apply _ _` which gives `volume(support f ∩ S) ≤ (volume.restrict S)(support f)`
- Chain: show `S ⊆ support f`, then `volume(S ∩ S) = volume(S) ≤ volume(support f ∩ S) ≤ restricted measure`

## ENNReal.mul_pos expects ≠ 0 arguments
- `ENNReal.mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b`
- Convert from `0 < x` via `ne_of_gt`: `ENNReal.coe_ne_zero.mpr (ne_of_gt ...)`

## Chained dot notation in Lean 4
- `.foo.bar.baz` can fail if `bar.baz` isn't atomic — explicit form is safer
- BUT pipe `|>.nnnorm.coe_nnreal_ennreal.pow_const _` works reliably
- Use `|>` to break the chain when direct dot notation misbehaves

## ENNReal rpow vs npow in lintegral
- In `∫⁻ u, ‖...‖₊ ^ (2 : ℝ)`, `‖...‖₊ : NNReal`, `^ (2:ℝ)` is NNReal.rpow, then coerced to ENNReal
- After `simp` or `set`, Lean may convert `^ (2:ℝ)` to `^ (2:ℕ)` (npow) in the goal
- Both are equal, but helper lemmas must match the goal type — check with `lean_goal`
- `by_cases` on set membership + `simp [indicator_of_mem, indicator_of_notMem]` handles both forms

## ENNReal finiteness for bounded integrals
- `inner_integral_one_lt_top` pattern: bound integrand by sum of indicators of I and (shift ⁻¹' I)
- `lintegral_add_right` splits the integral, `lintegral_indicator_one` converts to measure
- `measurePreserving_sub_const` shows preimage of I under shift has same measure as I
- `ENNReal.add_lt_top.mpr ⟨h1, h2⟩` for proving sum of two finite things is finite
- `ENNReal.mul_lt_top` for product; `ENNReal.coe_lt_top` for NNReal coercion
- `ENNReal.sum_lt_top.mpr` for finite sum: prove each summand `< ⊤`

## lintegral_mono is measure-agnostic
- `lintegral_mono (fun a => h a)` works for restricted integrals (`∫⁻ t in S, ...`)
- No need for `setLIntegral_mono_ae` when the pointwise bound holds everywhere (not just a.e.)
- `setLIntegral_mono_ae` requires `AEMeasurable` of upper bound; `lintegral_mono` doesn't

## lintegral_add_left takes Measurable, not AEMeasurable
- `lintegral_add_left (hf : Measurable f) g : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ`
- Works with restricted measure automatically (no `.aemeasurable.restrict` needed)
- Common mistake: passing `hf.aemeasurable` or `hf.aemeasurable.restrict` — just pass `hf`

## Weighted ENNReal inequality pattern
- For `w * a ≤ w * b₁ + w * b₂` from `a ≤ b₁ + b₂`:
  ```
  calc _ ≤ _ * (_ + _) := mul_le_mul' le_rfl h
    _ = _ + _ := mul_add _ _ _
  ```
- `mul_le_mul' le_rfl h` is the non-deprecated way (avoids `mul_le_mul_left'`)
- Two lines, works for both archEnergyIntegrand and primeEnergyTerm

## add_add_add_comm for energy form rearrangement
- `add_add_add_comm a b c d : (a + b) + (c + d) = (a + c) + (b + d)`
- Use after `add_le_add h_arch h_prime` to rearrange from (arch_B + arch_D) + (prime_B + prime_D)
  to (arch_B + prime_B) + (arch_D + prime_D) = E(B) + E(D)

## Indicator case analysis: include ALL membership facts in simp
- For `I.indicator`, `B.indicator`, `(I\B).indicator`: include simp lemmas for EVERY set
- Common mistake: forgetting `Set.indicator_of_notMem hvt_diff` for `(I\B).indicator` at points not in `I\B`
- Derived memberships (e.g., `u ∉ I \ B` from `u ∉ I`) must be established as `have` and included
