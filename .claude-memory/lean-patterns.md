# Lean & LSpec Patterns

## Finding Mathlib lemmas
- Use Loogle (https://loogle.lean-lang.org/) to search for Mathlib lemmas by type signature
- Example: search `Measurable (Real.exp)` to find `continuous_exp.measurable`
- Always check Loogle before guessing lemma names — Mathlib naming conventions are precise but not always predictable

## LSpec check' macro
- `check'` is compile-time only, produces `TestSeq`
- Must use `let t : TestSeq := check' "name" (prop)` — cannot chain directly with `++`
- `checkIO'` is the runtime variant (needed for configurable sample counts)

## Noncomputable barrier
- All Stage 1 definitions (dilationOp, mulConv, mulInvol, haarMult) are `noncomputable`
- This is inherent: they depend on Mathlib's real analysis (integrals, measures)
- `checkIO'` cannot evaluate noncomputable defs at runtime
- Current workaround: test Nat properties mirroring RPos group axioms
- Issues #10, #11 closed as "not planned" — Nat mirrors are sufficient

## RPos type
- `abbrev RPos := {x : ℝ // 0 < x}` — subtype, not a new type
- Has instances: One, Mul, Inv, Div, TopologicalSpace, MeasurableSpace
- `ℝ` equality is not `DecidableEq` so LSpec `test` can't check RPos value equalities directly

## Measurability of subtype maps
- For standard functions restricted to subtypes like RPos, use `Continuous.measurable` + `.subtype_mk`
- Example: `continuous_exp.measurable.subtype_mk` proves `Measurable expToRPos`
- `continuous_log'` gives measurability of log on positive reals

## MeasurableEquiv as a bridge
- Once you have `ℝ ≃ᵐ RPos`, properties transfer almost for free:
  - Sigma-finiteness: `equiv.sigmaFinite_map`
  - Measure pushforward manipulations
- Build equiv structures early — they pay off downstream

## Conjugation trick for Haar invariance
- To prove invariance of `haarMult` under multiplication by `a`:
  1. Rewrite image as preimage via `Set.image_eq_preimage_of_inverse`
  2. Conjugate RPos multiplication into ℝ translation via exp/log
  3. Appeal to `map_add_left_eq_self` (Lebesgue translation invariance)
- Same pattern works for `dilationOp_norm_eq` (L² isometry of dilation)

## lintegral_map_equiv coercion gotcha
- `lintegral_map_equiv f g` pattern-matches `∫⁻ x, f x ∂map ⇑g μ` (syntactic)
- `haarMult = map expToRPos volume` but `⇑expEquivRPos ≠ expToRPos` syntactically
- Fix: use `have h := lintegral_map_equiv _ expEquivRPos` with `exact` (definitional eq), then `rw [h]`
- Never `rw [lintegral_map_equiv]` directly when the measure uses a plain function instead of a MeasurableEquiv coercion

## norm_cast requires imported lemmas
- `norm_cast` can only use `@[norm_cast]`-tagged lemmas that are **imported**
- Key example: `integral_ofReal` (in `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`) lets `norm_cast` pull `↑` out of `∫ y, ↑(f y) ∂μ` — but only if imported
- `norm_cast` CAN look through integral binders (it's not limited to flat expressions)
- Symptom when import is missing: `norm_cast` normalizes internal casts (e.g. `↑x ^ 2` → `↑(x^2)`) but leaves the outer structure unchanged

## Goal probing technique
- To see an intermediate goal state, replace `sorry` with `exact (0 : ℕ)` — the type mismatch error displays the full goal
- Faster than adding `#check` or `trace` statements

## MeasurePreserving for RPos division
- To prove `MeasurePreserving (· / a) haarMult haarMult`, use the two-field constructor:
  - Measurability: `(measurable_subtype_coe.div_const a.val).subtype_mk`
  - Map equality: chain `map_map` → conjugation via `expToRPos_sub_log` → `← map_map` → `congr 1` → translation invariance
- `measurable_sub_const c` exists (additive version of `measurable_div_const`)
- Then `MemLp.comp_measurePreserving` transfers L² membership through the preserved map

## Hölder inequality for L² functions
- `MemLp.integrable_mul` : `MemLp f 2 μ → MemLp g 2 μ → Integrable (f * g) μ`
- Requires `HolderTriple 2 2 1` (auto-resolved)
- `MemLp.star` : `MemLp f p μ → MemLp (star f) p μ`
- Both need import `Mathlib.MeasureTheory.Function.L1Space.Integrable`

## lintegral_add_left_eq_self tips
- Requires `IsAddLeftInvariant μ` — provide `(μ := (volume : Measure ℝ))` explicitly when volume is implicit
- Higher-order unification may fail: provide `f` and the translation constant explicitly
- Use `simp_rw [sub_eq_add_neg, add_comm _ (-c)]` to get the `(-c + u)` form it expects

## Integrable dot-notation gotcha
- `Integrable` is a `def` (not `structure`) that unfolds to `AEStronglyMeasurable ∧ HasFiniteIntegral`
- Dot notation like `h_int.some_method` may resolve to `And.some_method` instead of `Integrable.some_method`
- Fix: use explicit namespace — `Integrable.congr h_int ...` instead of `h_int.congr ...`
- For composing with measure-preserving maps: `MeasurePreserving.integrable_comp_of_integrable` (NOT `Integrable.comp_measurePreserving` which doesn't exist)

## starRingEnd vs star
- `starRingEnd R x = star x` by `rfl` (via `starRingEnd_apply`)
- But `rw [norm_star]` does syntactic matching for `‖star ?x‖`, won't match `‖(starRingEnd ℂ) z‖`
- Fix: `rw [starRingEnd_apply, norm_star]` — first convert to `star`, then apply norm lemma

## let-bound MeasurableEquiv in proofs
- `let divEquiv : RPos ≃ᵐ RPos := ...` doesn't auto-unfold in goals
- `⇑divEquiv x` won't syntactically match `x / a` even though definitionally equal
- For `rw`: define `h_eq : ∀ y, ⇑divEquiv y = y / a := fun _ => rfl` then `simp_rw [h_eq]`
- For `integral_comp'`: use `simp_rw` to rewrite `x / a` to `⇑divEquiv x` BEFORE `exact`
- `mul_comm` needs type annotation `(G := ℂ)` when type inference is ambiguous

## Lean 4 parsing quirks

### `let` body starting with negation
- `let x := e; -body` fails to parse — Lean doesn't recognize `-body` as the continuation
- Fix: wrap in parens `((-x) + y)` or use `0 - x + y`
- Example that fails: `let c := 1; -(c + 2) + x`
- Example that works: `let c := 1; (-(c + 2) + x)`

### `set_option ... in` is a declaration modifier
- `set_option maxHeartbeats N in` must appear BEFORE the docstring, not between docstring and `theorem`
- Wrong: `/-- doc -/ set_option ... in theorem ...` (parse error: "expected 'lemma'")
- Right: `set_option ... in /-- doc -/ theorem ...`
- The comment explaining the heartbeat change goes between `set_option ... in` and the docstring

### `∂volume` in multi-line set integrals
- `∫ t in S, f t ∂volume` works on one line but fails when the integrand spans lines
- Fix: omit `∂volume` (volume is the default measure) or use `let` bindings for each integral
- Example: `let tail := ∫ t in Ici (2 * L), f t` then use `tail` in the expression

## Normal contraction / Lipschitz patterns
- No `Real.lipschitzWith_abs` in Mathlib — two options:
  (a) Manual: `LipschitzWith.of_dist_le_mul` + `abs_abs_sub_abs_le_abs_sub` (no extra imports)
  (b) Rewrite: `lipschitzWith_one_norm` + `Real.norm_eq_abs` (needs `Mathlib.Analysis.Normed.Field.Basic`)
- `Complex.nnnorm_real (r : ℝ) : ‖↑r‖₊ = ‖r‖₊` (in `Mathlib.Analysis.Complex.Norm`)
- `Set.indicator_comp_of_zero` composes: apply twice for `Φ` then `(↑· : ℝ → ℂ)` to bridge
  `zeroExtend (liftReal (Φ ∘ G)) I` to `fun u => ↑(Φ (I.indicator G u))`
- `LipschitzWith.dist_le_mul` gives `dist (f x) (f y) ≤ K * dist x y`; for K=1,
  `simp` reduces `↑1 * dist x y` to `dist x y`
- `NNReal.rpow_le_rpow` needs import `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- `IsCompact.infDist_compl_pos` does NOT exist in Mathlib — use direct arithmetic
  (`min(a - α, β - b) > 0` with `linarith`) for compact-in-open distance bounds

## `gcongr` for weighted ENNReal inequalities
- `gcongr` decomposes `c * ∫ ‖f‖₊^2 ≤ c * ∫ ‖g‖₊^2` into pointwise `‖f x‖₊ ≤ ‖g x‖₊`
- Handles the `mul_le_mul`, `lintegral_mono`, `rpow_le_rpow`, and `coe_le_coe` chain automatically
- Much cleaner than manual `unfold` + `mul_le_mul_left'` (which is deprecated → use `mul_le_mul_right`)
- Can be expensive: `archEnergyIntegrand` and `primeEnergyTerm` need `set_option maxHeartbeats 800000`
- **Key pattern**: factor out the pointwise nnnorm lemma as a named lemma, then `gcongr; exact myLemma _ _`
  - Inlining the proof causes heartbeat timeout; named lemma + wildcards lets Lean unify incrementally

## ae_restrict_of_ae_restrict_of_subset pattern
- Signature: `s ⊆ t → (∀ᵐ x ∂μ.restrict t, p x) → ∀ᵐ x ∂μ.restrict s, p x`
- **Don't use `apply`** — Lean can't infer the intermediate set `t`, leaving opaque `?t` metavariables
- **Do use `have h_sub : S ⊆ T := ...; exact ae_restrict_of_ae_restrict_of_subset h_sub h_ae`**
- Same principle as the `Integrable` dot-notation gotcha: spell out intermediate types explicitly

## Import for `volume` on ℝ
- `Mathlib.MeasureTheory.Measure.Restrict` + `Bochner.Basic` do NOT provide `volume` on `ℝ`
- Need `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` (or a transitive import that brings it in)
- Symptom: `failed to synthesize instance of type class MeasureSpace ℝ`

## Mathlib lemma name gotchas (as of v4.28)
- `div_lt_iff` doesn't exist — use `div_lt_iff₀` (with subscript zero)
- `Real.sinh_pos_iff` exists in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv` but is NOT accessible via `.mpr` from `DerivHyp` alone — prove sinh positivity from `Real.sinh_eq` + `exp_strictMono` instead
- `exp_le_one_of_nonpos` doesn't exist — use `Real.exp_le_exp.mpr` + `Real.exp_zero` calc chain

## Proving bounds on special functions

### sinh t ≥ t (for t ≥ 0)
- Use `mul_sub_le_image_sub_of_le_deriv` (MVT): sinh is differentiable, deriv = cosh ≥ 1, sinh(0) = 0
- Key imports: `Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp`, `Mathlib.Analysis.Calculus.MeanValue`
- Key lemmas: `Real.differentiable_sinh`, `Real.deriv_sinh`, `Real.one_le_cosh`

### sinh t > exp t / 4 (for t ≥ 1)
- Use `nlinarith` with hints: `sq_nonneg (Real.exp t)`, `Real.exp_pos (-t)`, and `exp t ≥ 2` (from `add_one_le_exp`)
- The `exp(t) * exp(-t) = 1` identity via `← Real.exp_add; simp`

### Cancellation proofs (exp products)
- `field_simp` + `rw [← Real.exp_add]; simp` handles most exp cancellations automatically
- Much cleaner than manual `div_mul_eq_mul_div` / `mul_div_assoc` chains

## Integrability proof patterns

### Domination-based (`Integrable.mono'`)
- For integrability on unbounded sets (e.g. `Ioi a`), dominate by a known integrable function
- Pattern: `apply Integrable.mono' h_dominator_integrable h_aestronglymeasurable h_ae_bound`
- Example: `1/sinh t` dominated by `4*exp(-t)` using `integrableOn_exp_neg_Ioi`
- For the ae-bound: `rw [ae_restrict_iff' measurableSet_Ioi]` then `Filter.Eventually.of_forall`

### Bounded-on-finite-measure (`IntegrableOn.of_bound`)
- For integrability on bounded/finite-measure sets
- Signature: `IntegrableOn.of_bound (hs : μ s < ⊤) (hf : AEStronglyMeasurable ...) (C : ℝ) (hfC : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C)`
- Use `refine` (not `apply`) because `C` is a term argument mixed with prop arguments
- Example: correction integrand bounded by `exp(L)/2` on `Ioc 0 (2L)` with `measure_Ioc_lt_top`

### Parameter-dependent integrals (`Measurable.lintegral_prod_right`)
- To prove `Measurable (fun x => ∫⁻ y, f x y ∂ν)`, show `Measurable (Function.uncurry f)`
- For `f(u - t)` jointly measurable in `(t, u)`: `h_f.comp (measurable_snd.sub measurable_fst)`
- Then `.nnnorm.coe_nnreal_ennreal.pow_const _` for the `‖·‖₊ ^ 2` wrapper
- Import: `Mathlib.MeasureTheory.Measure.Prod` (often transitively available)

## Name collision prevention
- Before declaring a theorem, use `lean_local_search` to check if the name already exists
- Example: `translationOp_zero` already existed (meaning "translate by 0 is identity") — my `translationOp t 0 = 0` caused a duplicate declaration error
- Convention: use `_apply_zero_fun` suffix for "applying to the zero function" vs plain `_zero` for "zero parameter"

## Set.indicator_zero' and simp power
- `Set.indicator_zero'` (note the prime) proves `Set.indicator s 0 = 0` — simp knows this
- When the function is literally `0`, `simp [zeroExtend_zero]` can close goals involving `translationOp t (zeroExtend 0 I)` without needing an explicit `translationOp_apply_zero_fun` lemma
- Don't pre-write helper lemmas — check if `simp` already handles the goal first via `lean_multi_attempt`

## integral_div and integral_add
- `integral_div` (Bochner/Basic.lean): `∫ f(x)/r = (∫ f)/r` — pulls constant division out
- `integral_add h_f h_g`: splits `∫ (f + g)` into `∫ f + ∫ g` (needs integrability of both)
- Common pattern: `rw [integral_div, integral_add h1 h2]` to go from `∫ (f+g)/c` to `(∫f + ∫g)/c`

## Transferring ae properties through translations
- **`measure_preimage_add_right`**: `volume ((· + c) ⁻¹' s) = volume s` — key for translation invariance
- Pattern for forward shift of ae property:
  1. Unwrap `∀ᵐ` via `rw [Filter.Eventually] at h ⊢`
  2. `apply Filter.mem_of_superset (x := (· + t) ⁻¹' S)`
  3. Show preimage is in ae: `rw [mem_ae_iff, ← Set.preimage_compl, measure_preimage_add_right]`
  4. Show inclusion with `intro x hx hx_mem` + `linarith`
- Do NOT use `ae_map_iff` — it requires `MeasurableSet` of the property set, which typically isn't available
- `Filter.mem_of_superset` parameter names: `x` (the superset), `hx` (membership), `hxy` (inclusion)

## Interval integral change of variables
- `integral_comp_add_right f d : ∫ x in a..b, f(x+d) = ∫ x in (a+d)..(b+d), f x`
- `integral_comp_sub_right f d : ∫ x in a..b, f(x-d) = ∫ x in (a-d)..(b-d), f x`
- Use `← integral_comp_add_right f t` to go from shifted bounds back to shifted argument
- `intervalIntegral.integral_congr_ae` (fully qualified to avoid ambiguity with `MeasureTheory.integral_congr_ae`)
- For `uIoc` membership: `rw [Set.uIoc_of_le (by linarith)]` converts to `Ioc` when bounds are ordered

## Lebesgue differentiation on ℝ
- `IsUnifLocDoublingMeasure.ae_tendsto_average` gives convergence of ball averages ae
- Instance for `volume` on `ℝ`: needs `import Mathlib.MeasureTheory.Measure.Haar.NormedSpace`
  - The instance chain goes through Haar measure theory, NOT through `Doubling.lean`
- Bridge: `setAverage_eq` → `Real.closedBall_eq_Icc` → `intervalIntegral_eq_integral_uIoc` → `integral_Icc_eq_integral_Ioc` → `Real.volume_Icc` → `ring`
- `Measure.real` unfolds `volume.real` for `ENNReal.toReal`

## ENNReal and measure-zero patterns
- **`linarith` does NOT work on ENNReal.** For `volume ... = 0` vs `0 < volume ...`, use `exact absurd this (ne_of_gt h_vol_pos)` — NOT `linarith`.
- **`ne_of_gt` convention**: `ne_of_gt : a < b → b ≠ a` (NOT `a ≠ b`). So `ne_of_gt (h : 0 < volume S)` gives `volume S ≠ 0`. No `.symm` needed.
- **`measure_mono_null`** (`s ⊆ t → μ t = 0 → μ s = 0`): much cleaner than `le_antisymm (le_trans (measure_mono ...) (by rw [...])) (zero_le _)`.
  - **Don't `apply measure_mono_null _ h`** when sets are described differently — Lean can't unify `{a | ¬P a}` with `S \ T`. Instead, pre-prove subset as `have h_sub : ... ⊆ ... := by ...` then `exact measure_mono_null h_sub h`.
- **Degenerate Icc volume**: `volume (Icc a b) = 0` when `b ≤ a` — use `simp only [Real.volume_Icc]; exact ENNReal.ofReal_of_nonpos (by linarith)`.
- **`gcongr` for Icc monotonicity**: `apply Icc_subset_Icc <;> gcongr` handles division-based endpoint monotonicity automatically. No need for manual `add_le_add_left` + `div_le_div_of_nonneg_left`.
- **`nlinarith` needs division pre-digested**: To go from `3/(β-α) < N` to `3 ≤ (β-α)*(N+2)`, first extract `3 < (β-α)*N` via `rwa [div_lt_iff₀' ...] at hN`, then `nlinarith` can handle the rest.

## simp only vs unfold for definitions with `let`
- **`simp only [defName]` > `unfold defName`** when definitions contain `let L := ...` bindings
- `unfold` does delta-reduction but may leave `have L := ...` in the goal (not beta-reduced)
- `simp only [defName]` treats the def as a rewrite rule AND beta/zeta-reduces the `let` binding
- This avoids naming conflicts when you've also done `set L := ...` locally

## setLIntegral naming
- **`setLIntegral_congr_fun`** changes the *integrand*: `MeasurableSet s → EqOn f g s → ∫⁻ x in s, f x = ∫⁻ x in s, g x`
- **`setLIntegral_congr`** changes the *set*: `s =ᶠ[ae μ] t → ∫⁻ x in s, f x = ∫⁻ x in t, f x`
- The naming is counterintuitive — always check the signature

## Extracting helpers to avoid set/unfold mismatch
- When `set φ := expr` + `unfold defName` causes expression matching failures (new occurrences of `expr` appear that `set` didn't replace), extract the problematic subgoal into a `private theorem` with explicit types
- This gives a clean interface: the helper's type signature forces Lean to match correctly

## setIntegral_congr_fun and beta-reduction
- **Name**: `setIntegral_congr_fun` (NOT `setIntegral_congr`) — for pointwise equality on a measurable set → integral equality
- Signature: `MeasurableSet s → Set.EqOn f g s → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`
- **Beta-reduction gotcha**: The resulting goal is `(fun x => ...) t = (fun x => ...) t` with unapplied lambdas
- Must add `simp only` before `congr 1` to beta-reduce, otherwise `rw` can't find patterns in the goal
- Correct pattern:
  ```lean
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  simp only        -- beta-reduce the lambdas
  congr 1
  rw [...]         -- now pattern matching works
  ```
- `setIntegral_nonneg` (for nonneg integrals) does NOT have this issue — its goal is direct

## Division/inversion algebra in inequalities
- When proving inequalities involving `x + x⁻¹` or `(a + a⁻¹)/2 ≤ b`:
  - **Don't** try to chain `rw` through `inv_le_comm₀`, `div_le_iff₀`, etc. — term structure mismatches are painful
  - **Do** prove an algebraic identity with `field_simp; ring` to convert to polynomial form, then use `nlinarith`
  - Pattern: `have h_eq : lhs = polynomial_form / denom := by field_simp; ring` then `rw [h_eq]; exact div_nonneg ... ...`
  - Example: `v*2 - (v*v + (v*v)⁻¹) = (2*v^3 - v^4 - 1) / v^2` by `field_simp; ring`
- `nlinarith [sq_nonneg x, sq_nonneg (x - c)]` is very powerful for polynomial inequalities — feed it strategic squares
- `div_le_div_iff₀` can produce `a * d ≤ b * c` with operands in unexpected order — use `linarith` to rearrange

## Mathlib name patterns for hyperbolic functions
- `Real.continuous_cosh` / `Real.continuous_sinh` (NOT `continuousOn_` variants — those don't exist)
- `Real.sinh_nonneg_iff` / `Real.sinh_pos_iff` (in `Trigonometric.Deriv`, NOT `sinh_pos_of_pos`)
- `Real.exp_one_lt_d9` (in `Mathlib.Analysis.Complex.ExponentialBounds`) — `exp 1 < 2.7182818286`
- `Real.one_le_exp` (for `0 ≤ x → 1 ≤ exp x`)
- `Real.exp_add` — the fundamental identity for `exp(a) * exp(b) = exp(a+b)`; use `← Real.exp_add` + `ring_nf`

## monotoneOn_of_deriv_nonneg pattern
- API: `monotoneOn_of_deriv_nonneg (convex D) (cont_on D) (diff_on interior_D) (deriv_nonneg interior_D)`
- The four arguments are: convexity, continuity on D, differentiability on interior D, nonneg deriv on interior D
- For `DifferentiableOn`: intro + `.differentiableWithinAt` on a `DifferentiableAt` proof
- For `deriv f x`: use `HasDerivAt.deriv` to rewrite `deriv f x` to the computed derivative
- `interior_Icc` converts membership in `interior (Icc a b)` to `Ioo a b` membership

## Import chain verification
- `lean_run_code` is a sandbox — it does NOT replicate the project's transitive dependency graph
- When using a definition from another stage (e.g. `energyForm` from Stage 2 in Stage 5), verify it's in the transitive import chain by grepping `^import` lines through the dependency path
- If not transitively available, add an explicit import (e.g. `import ConnesLean.Stage2.EnergyForm`)
- Example: `SymbolLowerBound → FourierSymbol → {ArchimedeanWeight, PrimeDistribution}` does NOT include `EnergyForm`
- Always do `lake build` early rather than trusting `lean_run_code` alone for import validation

## lintegral_indicator_one for bounded-set finiteness
- **`lintegral_indicator_one`**: `MeasurableSet s → ∫⁻ a, s.indicator 1 a ∂μ = μ s`
- Much simpler than composing `lintegral_indicator` + `lintegral_const` + `one_mul`
- **`lintegral_indicator`**: `MeasurableSet s → ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ` — changes integral domain
- Key difference: `lintegral_indicator` needs a *function* argument `f`; `lintegral_indicator_one` works with the constant `1`
- **Pattern for bounded indicator finiteness**: prove pointwise `‖φ u‖₊ ^ 2 ≤ I.indicator 1 u`, then `lintegral_mono` + `lintegral_indicator_one` + `measure_Ioo_lt_top`
- **`logInterval`** uses `Ioo` (open interval), NOT `Icc` — use `measure_Ioo_lt_top` for finiteness, not `volume_Icc`

## Double indicator `split_ifs` pattern
- For `zeroExtend (B.indicator f) I` = `I.indicator (B.indicator f)`:
  - First `split_ifs with hI` (outer set membership)
  - Then `split_ifs with hB` (inner set membership)
  - One-shot `simp` rarely works because `Set.indicator` doesn't simplify without knowing membership
- Pre-prove pointwise bound as `have h_le : ∀ u, ... ≤ ...` then feed to `lintegral_mono`

## Axiom design: weaker is better
- Axioms should have the *weakest* hypotheses needed (closest to the actual theorem)
- Adding hypotheses like `Measurable φ` and `∫⁻ ‖φ‖₊² < ⊤` makes the axiom match the standard mathematical statement
- Stronger-than-needed axioms (e.g., `∀ φ : ℝ → ℂ` without measurability) add unnecessary logical strength
- This is opposite to theorems, where stronger conclusions are better

## Nat.floor for telescoping arguments
- Import: `Mathlib.Algebra.Order.Floor.Defs` (definition), lemmas in `Mathlib.Algebra.Order.Floor.Semiring`
- `Nat.floor_le (h : 0 ≤ x) : ↑⌊x⌋₊ ≤ x` — convert via `(le_div_iff₀ hpos).mp`
- `Nat.lt_floor_add_one x : x < ↑⌊x⌋₊ + 1` — convert via `(div_lt_iff₀ hpos).mp`
- Pattern: set `n := ⌊gap / step⌋₊`, prove `n * step ≤ gap < (n+1) * step`, induct on `n`

## ENNReal top-absorption lemmas
- **`WithTop.add_top`**: `(x : WithTop α) → x + ⊤ = ⊤` — works for ENNReal since `ENNReal = WithTop ℕ∞`
- There is NO `ENNReal.add_top` — must use `WithTop.add_top`
- **`ENNReal.add_ne_top`**: `a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤` — but `Iff.not_iff` doesn't exist, so can't negate it directly
- **Proof pattern for "sum finite ⇒ both summands finite"**: instead of negating the iff, rewrite with the top value then use `rfl`:
  ```lean
  rw [h_split, h_top, WithTop.add_top] at hG_fin
  exact hG_fin rfl
  ```

## Import chain gotchas
- **Always verify the actual transitive import chain** before using a theorem from another file
- `lean_local_search` finding a name does NOT mean it's importable — it searches all project files
- Example: `InvarianceSplit` imports `CompactResolvent`, NOT `IndicatorEnergy` — so `symm_diff_logInterval_measure` from IndicatorEnergy is not available via InvarianceSplit alone
- Fix: add explicit `import ConnesLean.Stage6.IndicatorEnergy` when needed
- **`lean_run_code` is not representative**: it has all of Mathlib available; your file only has its transitive imports

## Set vs Finset namespace ambiguity
- Opening both `Finset` and `Set` causes ambiguity for `mem_Ioo`, `preimage`, `Ioo`, etc.
- `mem_Ioo` resolves to both `Set.mem_Ioo` and `Finset.mem_Ioo`
- `preimage` resolves to both `Set.preimage` and `Finset.preimage`
- Fix: qualify with `Set.mem_Ioo`, `Set.preimage`, `Set.Ioo` etc.
- Or avoid opening `Finset` if not needed (use `Finset.sum` explicitly)

## `rw` with complex set expressions is fragile
- When the target set involves lambdas or preimages, `rw [myLemma]` often fails to unify
- Pattern: `set B' : Set ℝ := (· - t) ⁻¹' S` then `have h_eq : integral = volume (symmDiff A B') := ...` then `rw [h_eq]`
- Alternatively: use `change` to restate the goal with the expected types
- For ENNReal coercions: `↑(x.toNNReal) = ENNReal.ofReal x` holds by `rfl`, so `change` can switch between them

## Mathlib lemma name gotchas (as of v4.28) — continued
- `div_le_iff` doesn't exist — use `div_le_iff₀` (with subscript zero)
- `ENNReal.coe_toNNReal_eq_toNNReal` doesn't exist — `ENNReal.ofReal x = ↑(x.toNNReal)` by `rfl`

## ENNReal indicator elaboration patterns

### `≤ᵐ[μ]` must be on one line
- `f ≤ᵐ[volume.restrict S] g` works
- `f ≤ᵐ\n  [volume.restrict S]\n  g` fails with "elaboration function not implemented"
- The superscript notation parser doesn't handle line breaks between `≤ᵐ` and `[μ]`

### `.indicator` on new line resolves wrong
- `(logInterval L \ B)\n  .indicator f` resolves `.indicator` as `Real.indicator` (from `open Real`)
- Fix: put `.indicator` on same line as the closing paren: `(logInterval L \ B).indicator f`

### `Set.indicator_of_notMem` takes explicit function argument
- Signature: `indicator_of_notMem (h : a ∉ s) (f : α → M) : s.indicator f a = 0`
- `indicator_of_notMem h_nmem` alone gives `∀ (f : ...), ...`, not a specific equality
- Must write: `indicator_of_notMem h_nmem (1 : ℝ → ENNReal)` for indicator with value 1

### `Pi.one_apply` universe polymorphism
- `Pi.one_apply u : (1 : α → M) u = 1` — but Lean may not unify `M` with `ENNReal`
- Symptom: "expected `ℝ≥0∞ = 1 u`" type mismatch
- Fix: avoid `Pi.one_apply`; instead use `rw [indicator_of_mem h]; simp` and let Lean figure out types

### Bounding `∫⁻ ‖φ(u) - φ(u-t)‖₊²` for finiteness
- DON'T bound by `I.indicator 1` alone — fails when `u ∉ I` but `u-t ∈ I`
- DO bound by `(I ∪ (· - t) ⁻¹' I).indicator 1` — covers all 4 cases
- Then: `lintegral_indicator_one` + `measure_union_le` + finiteness of each piece

### ENNReal finiteness from sum via `ne_top_of_le_ne_top`
- To show summand is finite when sum is finite:
  ```lean
  ne_top_of_le_ne_top hE le_self_add  -- arch ≤ arch + prime = E ≠ ⊤
  ```
- Cleaner than `intro h; rw [h]; exact top_add _` which fights with `set L` aliases

## `show` vs `change` linter (Lean 4 / Mathlib v4.28)
- `show` is now linted: "The `show` tactic should only be used to indicate intermediate goal states for readability"
- When the tactic actually modifies the goal (e.g., unfolding `formDomain` to `energyForm ... ≠ ⊤`), use `change` instead
- `show` is fine when it matches the current goal exactly (just for documentation)
