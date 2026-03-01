# The `noncomputable` Barrier in ConnesLean

## What `noncomputable` means in Lean 4

Lean 4 serves two roles: a **programming language** that compiles to executable code, and a **proof assistant** that verifies mathematical reasoning at compile time. These two roles have different requirements.

When a definition relies on the axiom of choice (`Classical.choice`) or other non-constructive principles, Lean marks it `noncomputable`. This means:

- The definition is **logically valid** — Lean's kernel fully trusts it for proofs.
- The definition has **no executable code** — `#eval` and runtime operations cannot use it.

Mathlib's real number type `ℝ` is built on Cauchy sequences with classical quotients, making it inherently noncomputable. Any definition that touches `ℝ`, its measure theory, or its integration theory inherits this constraint.

This is a **permanent structural property of the formalization**, not a bug to fix.

## Why everything in ConnesLean is noncomputable

The noncomputability propagates through a dependency chain rooted in `ℝ`. In Stage 1 this looks like:

```
ℝ (Mathlib, noncomputable)
 └─ RPos := {x : ℝ // 0 < x}               ConnesLean/Stage1/MultiplicativeHaar.lean:45
     ├─ expToRPos / logFromRPos              ConnesLean/Stage1/MultiplicativeHaar.lean:82,85
     ├─ haarMult : Measure RPos              ConnesLean/Stage1/MultiplicativeHaar.lean:127
     │   └─ Measure.map expToRPos volume     (pushforward of Lebesgue measure)
     ├─ dilationOp (a : RPos)                ConnesLean/Stage1/DilationOperator.lean:45
     ├─ mulConv (g h : RPos → ℂ)            ConnesLean/Stage1/Convolution.lean:44
     └─ mulInvol (g : RPos → ℂ)             ConnesLean/Stage1/Convolution.lean:50
```

This propagation extends through all subsequent stages:

| Stage | Files | Noncomputable? | Key definitions |
|-------|-------|----------------|-----------------|
| Stage 1 | 5 files + `UnitaryIdentity.lean` | All except `UnitaryIdentity.lean` | `RPos`, `haarMult`, `dilationOp`, `mulConv`, `mulInvol` |
| Stage 2 | 7 files | All | `translationOp`, `logCoord`, `primeDistribution`, `archimedeanWeight`, `energyForm` |
| Stage 4 | 5 files | All | `markovProjection`, `mollificationConstancy`, `translationInvariance` |
| Stage 5 | 5 files | All | `fourierSymbol`, `closedForm`, `compactEmbedding`, `compactResolvent` |
| Stage 6 | 4 files | All | `indicatorEnergy`, `energyPositivity`, `invarianceSplit`, `constantInDomain` |

Every `.lean` file across Stages 1–6 opens a `noncomputable section`, with a single exception:

**The exception**: `UnitaryIdentity.lean` states its theorems for an abstract Hilbert space (`E` with `InnerProductSpace ℂ E`), with no dependence on measures or `ℝ`-valued functions. It is the only file that avoids the noncomputable barrier.

## What still works

Noncomputable definitions are fully usable for **proving theorems**. The following all work normally:

| Technique | Example |
|---|---|
| `theorem` / `example` declarations | `example : dilationOp 1 g = g := dilationOp_one g` |
| Compile-time type checking | `lake build ConnesLean` verifies all types match |
| Tactic proofs | `rfl`, `simp`, `linarith`, `ring`, `norm_num`, `congr`, `ext` |
| Definitional unfolding | `rfl` can prove `dilationOp a g x = g (x / a)` |

The compile-time test files in `ConnesLeanTest/` demonstrate this: they use `example` blocks that Lean checks during `lake build`, verifying properties without needing runtime execution.

## What doesn't work

| Blocked operation | Why |
|---|---|
| `#eval` on any `RPos` or `haarMult` expression | No compiled code exists |
| LSpec `checkIO'` with noncomputable functions | `checkIO'` needs runtime evaluation |
| LSpec `test` comparing `RPos` values for equality | `ℝ` has no `DecidableEq` instance |
| Runtime property-based testing over `RPos` | SlimCheck cannot generate `RPos` samples without computable arithmetic |

## Testing strategies and workarounds

### 1. Compile-time `example` proofs (current)

Files: `ConnesLeanTest/Stage1Tests.lean` through `ConnesLeanTest/Stage6Tests.lean`

These are checked by Lean's kernel during `lake build`. They verify real theorems about the actual noncomputable definitions:

```lean
-- RPos arithmetic
example : (1 : RPos).val = 1 := rfl
example : ((⟨2, by norm_num⟩ : RPos) * ⟨3, by norm_num⟩).val = 6 := by
  simp [RPos.mul_val]; norm_num

-- Dilation operator
example (g : RPos → ℂ) : dilationOp 1 g = g := dilationOp_one g
example (a : RPos) (g : RPos → ℂ) : dilationOp a⁻¹ (dilationOp a g) = g :=
  dilationOp_inv a g
```

**Strength**: Tests the actual definitions across all stages. **Limitation**: Only proves universally quantified statements; cannot do random sampling.

### 2. LSpec Nat mirrors (current)

File: `lspec/Main.lean`

The LSpec executable tests algebraic properties on `Nat` that mirror the `RPos` group axioms:

```lean
check' "mul_comm" (∀ n m : Nat, n * m = m * n)
check' "mul_assoc" (∀ a b c : Nat, (a * b) * c = a * (b * c))
```

**Strength**: Exercises the LSpec infrastructure and CI pipeline. **Limitation**: Tests `Nat`, not `RPos` — these are structural analogs, not direct tests.

### 3. Axiom soundness checks (current)

Files: `soundness/Main.lean`, `ConnesLeanTest/SoundnessTests.lean`

The soundness executable inventories all project axioms and verifies that compile-time test tautologies do not depend on `sorryAx`. CI runs `lake exe soundness_check` and also greps build output for `sorryAx` to catch proof gaps.

**Strength**: Ensures no `sorry` leaks through and all axioms are accounted for.

### 4. Computable wrappers (future, issue #11)

A future approach could define computable wrapper types backed by floating-point or rational arithmetic for runtime testing, while keeping the noncomputable `ℝ`-based definitions for proofs. This is tracked in GitHub issue #11.

## Proof completion status

All theorems in Stages 1–6 are **fully proved** — there are zero `sorry` statements in the codebase. This includes the foundational Haar measure properties that were previously the most challenging gaps:

| Theorem | File | Status |
|---|---|---|
| `measurable_expToRPos` | `MultiplicativeHaar.lean:104` | Proved via `continuous_exp.measurable.subtype_mk` |
| `measurable_logFromRPos` | `MultiplicativeHaar.lean:108` | Proved via `continuous_log'.measurable` |
| `haarMult_sigmaFinite` | `MultiplicativeHaar.lean:132` | Proved via `expEquivRPos.sigmaFinite_map` |
| `haarMult_mul_invariant` | `MultiplicativeHaar.lean:139` | Proved via conjugation to Lebesgue translation invariance |
| `dilationOp_norm_eq` | `DilationOperator.lean:86` | Proved via exp equivalence + Lebesgue translation |
| `inner_dilationOp_le` | `DilationOperator.lean:112` | Proved via AM-GM + measure preservation |
| `convolution_at_one` | `ConvolutionInnerProduct.lean:110` | Proved via `mul_conj` + lintegral conversion |
| `convolution_inv_eq_conj` | `ConvolutionInnerProduct.lean:65` | Proved via change of variables + `integral_conj` |
| `mulConv_mulInvol_integrable` | `Convolution.lean:87` | Proved via Hölder (L² × L² → L¹) |

## Project axioms (distinct from `sorry`)

The project uses 10 explicitly declared `axiom` statements in Stages 2, 5, and 6. These are not proof gaps — they are clearly stated mathematical assumptions that will be proved in Phase 2 (axiom elimination). Each axiom carries a `**Soundness:**` annotation explaining its justification. See `docs/axiom-soundness-convention.md` and `docs/axiom-elimination-roadmap.md` for details.

Stages 1 and 4 are fully axiom-free (beyond Lean's standard `Classical.choice`, `propext`, `Quot.sound`).

## Future directions

- Computable wrapper types (issue #11) could enable runtime sanity checks, but the canonical proofs will always use the noncomputable Mathlib definitions.
- Phase 2 (axiom elimination) will replace the 10 project axioms with Lean proofs. The noncomputable constraint will remain — it is inherent to formalizing analysis over `ℝ` in Lean/Mathlib.
- The axiom elimination roadmap (`docs/axiom-elimination-roadmap.md`) prioritizes the most impactful axioms first.
