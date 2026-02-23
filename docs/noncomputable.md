# The `noncomputable` Barrier in ConnesLean

## What `noncomputable` means in Lean 4

Lean 4 serves two roles: a **programming language** that compiles to executable code, and a **proof assistant** that verifies mathematical reasoning at compile time. These two roles have different requirements.

When a definition relies on the axiom of choice (`Classical.choice`) or other non-constructive principles, Lean marks it `noncomputable`. This means:

- The definition is **logically valid** — Lean's kernel fully trusts it for proofs.
- The definition has **no executable code** — `#eval` and runtime operations cannot use it.

Mathlib's real number type `ℝ` is built on Cauchy sequences with classical quotients, making it inherently noncomputable. Any definition that touches `ℝ`, its measure theory, or its integration theory inherits this constraint.

This is a **permanent structural property of the formalization**, not a bug to fix.

## Why everything in Stage 1 is noncomputable

The noncomputability propagates through a dependency chain rooted in `ℝ`:

```
ℝ (Mathlib, noncomputable)
 └─ RPos := {x : ℝ // 0 < x}               ConnesLean/Stage1/MultiplicativeHaar.lean:35
     ├─ expToRPos / logFromRPos              ConnesLean/Stage1/MultiplicativeHaar.lean:72-75
     ├─ haarMult : Measure RPos              ConnesLean/Stage1/MultiplicativeHaar.lean:99
     │   └─ Measure.map expToRPos volume     (pushforward of Lebesgue measure)
     ├─ dilationOp (a : RPos)                ConnesLean/Stage1/DilationOperator.lean:33
     ├─ mulConv (g h : RPos → ℂ)            ConnesLean/Stage1/Convolution.lean:33
     └─ mulInvol (g : RPos → ℂ)             ConnesLean/Stage1/Convolution.lean:39
```

Every file in `ConnesLean/Stage1/` except `UnitaryIdentity.lean` opens a `noncomputable section` because it builds on `RPos` and `haarMult`.

**The exception**: `UnitaryIdentity.lean` states its theorems for an abstract Hilbert space (`E` with `InnerProductSpace ℂ E`), with no dependence on measures or `ℝ`-valued functions. It is the only Stage 1 file that avoids the noncomputable barrier.

## What still works

Noncomputable definitions are fully usable for **proving theorems**. The following all work normally:

| Technique | Example |
|---|---|
| `theorem` / `example` declarations | `example : dilationOp 1 g = g := dilationOp_one g` |
| Compile-time type checking | `lake build ConnesLean` verifies all types match |
| Tactic proofs | `rfl`, `simp`, `linarith`, `ring`, `norm_num`, `congr`, `ext` |
| `sorry` placeholders | Mark incomplete proofs; the file still compiles |
| Definitional unfolding | `rfl` can prove `dilationOp a g x = g (x / a)` |

The compile-time test file `test/Stage1Tests.lean` demonstrates this: it uses `example` blocks that Lean checks during `lake build`, verifying properties like `dilationOp 1 g = g` and `mulInvol (mulInvol g) = g` without needing runtime execution.

## What doesn't work

| Blocked operation | Why |
|---|---|
| `#eval` on any `RPos` or `haarMult` expression | No compiled code exists |
| LSpec `checkIO'` with noncomputable functions | `checkIO'` needs runtime evaluation |
| LSpec `test` comparing `RPos` values for equality | `ℝ` has no `DecidableEq` instance |
| Runtime property-based testing over `RPos` | SlimCheck cannot generate `RPos` samples without computable arithmetic |

## Testing strategies and workarounds

### 1. Compile-time `example` proofs (current)

File: `test/Stage1Tests.lean`

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

**Strength**: Tests the actual definitions. **Limitation**: Only proves universally quantified statements; cannot do random sampling.

### 2. LSpec Nat mirrors (current)

File: `lspec/Main.lean`

The LSpec executable tests algebraic properties on `Nat` that mirror the `RPos` group axioms:

```lean
check' "mul_comm" (∀ n m : Nat, n * m = m * n)
check' "mul_assoc" (∀ a b c : Nat, (a * b) * c = a * (b * c))
```

**Strength**: Exercises the LSpec infrastructure and CI pipeline. **Limitation**: Tests `Nat`, not `RPos` — these are structural analogs, not direct tests.

### 3. Computable wrappers (future, issue #11)

A future approach could define computable wrapper types backed by floating-point or rational arithmetic for runtime testing, while keeping the noncomputable `ℝ`-based definitions for proofs. This is tracked in GitHub issue #11.

## Outstanding `sorry` proofs

There are currently **9** `sorry` gaps in Stage 1. They form a dependency chain — the Haar measure properties are foundational, and the downstream theorems cannot be completed without them.

### Root: Haar measure properties (4 sorries)

All in `ConnesLean/Stage1/MultiplicativeHaar.lean`:

| Theorem | Line | Description |
|---|---|---|
| `measurable_expToRPos` | 87 | Measurability of `exp : ℝ → RPos` |
| `measurable_logFromRPos` | 91 | Measurability of `log : RPos → ℝ` |
| `haarMult_sigmaFinite` | 104 | Sigma-finiteness of `haarMult` |
| `haarMult_mul_invariant` | 111 | Left-invariance: `μ(a · S) = μ(S)` |

### Blocked: L² norm and integral theorems (3 sorries)

| Theorem | File | Line | Blocked by |
|---|---|---|---|
| `dilationOp_norm_eq` | `DilationOperator.lean` | 74 | `haarMult_mul_invariant` |
| `inner_dilationOp_le` | `DilationOperator.lean` | 84 | `dilationOp_norm_eq` |
| `convolution_at_one` | `ConvolutionInnerProduct.lean` | 75 | `haarMult_sigmaFinite` |

### Blocked: Convolution identities (2 sorries)

| Theorem | File | Line | Blocked by |
|---|---|---|---|
| `convolution_inv_eq_conj` | `ConvolutionInnerProduct.lean` | 52 | `haarMult_mul_invariant` |
| `mulConv_mulInvol_integrable` | `Convolution.lean` | 76 | `haarMult_sigmaFinite`, `measurable_*` |

## Future directions

- **All future Stages involving measures, integrals, or L² spaces will face the same constraint.** This is inherent to formalizing analysis over `ℝ` in Lean/Mathlib.
- Computable wrapper types (issue #11) could enable runtime sanity checks, but the canonical proofs will always use the noncomputable Mathlib definitions.
- The `sorry` dependency chain means that resolving the 4 Haar measure gaps will unblock most of the remaining 5 theorems. These are the highest-leverage targets for proof work.
