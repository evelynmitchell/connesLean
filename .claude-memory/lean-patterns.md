# Lean & LSpec Patterns

## Theorem vs Def
- If the return type is a `structure` (carries data, not `Prop`), use `def` not `theorem`. Lean rejects `theorem` for non-Prop types. Example: `ground_state_exists` returns `GroundState` (a structure), so it must be `def`.

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

## ENNReal cancellation for component equality
- Pattern: `a + b = c + d`, `a ≤ c`, `b ≤ d`, `a + b ≠ ⊤` → `a = c`
- Proof: `le_antisymm h_ac` then `(ENNReal.add_le_add_iff_right h_d_fin).mp h1`
  where `h1` is obtained by `rw [h_eq] at (add_le_add_right h_bd a)`
- Use `add_le_add_right` (NOT `add_le_add_left`) for `b ≤ d → a + b ≤ a + d`
- `ENNReal.mul_right_inj (h0 : a ≠ 0) (ht : a ≠ ⊤) : a * b = a * c ↔ b = c`

## ae equality → everywhere equality on open sets
- `Measure.eqOn_of_ae_eq : f =ᵐ[μ.restrict s] g → ContinuousOn f s → ContinuousOn g s → s ⊆ closure (interior s) → EqOn f g s`
- For open sets: `s ⊆ closure (interior s)` is `isOpen_Ioo.interior_eq ▸ subset_closure`
- `ae_eq_of_ae_le_of_lintegral_le : f ≤ᵐ g → ∫f ≠ ⊤ → AEMeasurable g → ∫g ≤ ∫f → f =ᵐ g`
  Note: reversed inequality direction on integrals

## lintegral_add_left matching
- `lintegral_add_left` infers `f` from the measurability proof type
- If `hf : Measurable (archEnergyIntegrand G L)`, then `rw [lintegral_add_left hf]` matches
  `∫ (archEnergyIntegrand G L t + g t)` correctly
- If `hf` is built from unfolded components, Lean infers `f` as the unfolded form → mismatch
- Fix: prove `hf : Measurable (archEnergyIntegrand G L)` as a named `have`, ensuring the type
- **`comp` in measurability breaks `rw` matching**: `hf.comp (measurable_id.sub measurable_const)`
  proves `Measurable (f ∘ (fun u => id u - t))` but `rw [lintegral_add_left hf_comp]` looks for
  `(f ∘ (fun u => id u - t)) u` in the goal, not `f (u - t)`. These are definitionally equal but
  `rw` doesn't handle that.
- **Best fix: `set fB := fun u => ...` then `lintegral_add_left hfB_meas`**: naming the function
  explicitly with `set` makes Lean resolve the match at definition time. After splitting, use
  `change` to convert to a named API form (e.g. `innerIntegral`).

## `set` local defs get unfolded by `unfold`/`simp`
- `set L := Real.log cutoffLambda` and `set I := logInterval L` create local defs
- `unfold innerIntegral` + `simp only [translationOp_apply]` will unfold `L` and `I` too,
  producing `logInterval (log cutoffLambda)` instead of `I` in hypotheses
- Then `change ... I ...` on a goal still using `I` fails (different normal forms)
- **Fix**: Don't unfold + simp on hypotheses to convert them. Instead, use `change` on the
  goal to match the API form, or use `set` + named lemma approach to avoid the mismatch.
- Alternative: manipulate at the `innerIntegral` level (don't unfold), then `change` to
  convert between raw integrand goals and the named API.

## `set` vs `let` aliasing in proofs
- `set gs := expr` creates an **opaque** local definition. If another function returns a `let`-bound value with the same underlying expression, `rw` and type unification may fail because the `set` alias isn't definitionally equal to the `let` binding.
- **Symptom**: "Application type mismatch" when passing a hypothesis proved about `set`-aliased terms to a function that expects the raw expression.
- **Fix 1**: Use `set gs := expr with gs_def` and `rw [gs_def]` to explicitly unfold when needed.
- **Fix 2**: Use `let` instead of `set` for transparent bindings (but `let` doesn't rewrite in the goal).
- **Fix 3**: Avoid aliasing entirely — work with the full expression `(ground_state_exists Λ hΛ).eigenfunction` directly.

## `rw` replaces ALL occurrences (both sides of goal)
- `rw [h]` where `h : a = b` replaces every `a` with `b` in the goal, including on the RHS.
- If the goal is `a = f a` and you `rw [h]` where `h : a = c·a`, you get `c·a = f (c·a)` (wrong).
- **Fix**: Use `calc` blocks for chained equalities, or `conv_lhs { rw [...] }` for targeted rewriting.

## ae transfer through negation on ℝ
- `Measure.IsNegInvariant volume` does NOT have an instance for Lebesgue measure on ℝ (as of Mathlib v4.28).
- **Workaround**: Use `Real.volume_preimage_mul_left` with `a = -1`:
  ```
  have : Neg.neg ⁻¹' S = (fun x => (-1 : ℝ) * x) ⁻¹' S := by ext x; simp
  rw [this, Real.volume_preimage_mul_left (by norm_num : (-1 : ℝ) ≠ 0)]
  simp [h]  -- |(-1)⁻¹| = 1, so measure is preserved
  ```

## sq_eq_one_iff for ℂ
- `sq_eq_one_iff : a ^ 2 = 1 ↔ a = 1 ∨ a = -1` requires `[Ring R] [NoZeroDivisors R]`
- ℂ has `NoZeroDivisors` (via `import Mathlib.Analysis.SpecialFunctions.Complex.Circle` or similar)

## Deriving contradiction from ae + positive-measure set
- Pattern: have `∀ᵐ x, x ∈ I → False` where `I` has positive measure.
- Proof: `rw [ae_iff]` gives `volume {x | ¬(x ∈ I → False)} = 0`, simplify set to `I`, then `absurd` with `ne_of_gt (volume_Ioo_pos)`.

## Indicator case analysis: include ALL membership facts in simp
- For `I.indicator`, `B.indicator`, `(I\B).indicator`: include simp lemmas for EVERY set
- Common mistake: forgetting `Set.indicator_of_notMem hvt_diff` for `(I\B).indicator` at points not in `I\B`
- Derived memberships (e.g., `u ∉ I \ B` from `u ∉ I`) must be established as `have` and included
