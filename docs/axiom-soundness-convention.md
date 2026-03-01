# Axiom Soundness Convention

## Why this exists

PR #91 revealed a subtle bug class: an axiom parameterized by a structure
with weak fields can be overpowered — any trivially-constructible instance
satisfies the preconditions, making the axiom grant conclusions for free.
The fix was folding the axiom into the structure, but we want to prevent
this class of bug going forward.

Every `axiom` declaration in ConnesLean must include a `**Soundness:**`
annotation in its docstring explaining why the axiom's preconditions are
adequate.

## The two categories

### 1. Bare-hypothesis axioms

The axiom takes scalar bounds, functions, and predicates that directly
match the mathematical theorem's hypotheses. Example:

```
/-- ...
    **Soundness:** Sole precondition is `1 < cutoffLambda`, matching
    Lemma 11. The existential conclusion cannot be vacuously satisfied.
    No structure parameters. -/
axiom fourierSymbol_ge_log (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) : ...
```

### 2. Structure-consuming axioms

The axiom takes a structure as a parameter. The structure must contain a
substantive field that cannot be trivially constructed (e.g., a proof of
an inequality, a convergence property). The annotation names the guarding
field. Example:

```
/-- ...
    **Soundness:** The `EnergyFormSplit` parameter requires a nontrivial
    `split_eq` field proving energy decomposition. Cannot be constructed
    without a genuine proof. -/
axiom some_future_axiom (s : EnergyFormSplit) : ...
```

If the structure has only `Prop`-valued fields with weak hypotheses (e.g.,
`Measurable f`), the axiom is likely overpowered and should be redesigned.

## How to write a soundness annotation

1. **List the preconditions.** What does the axiom require?
2. **Match to the math.** Which theorem/lemma in `lamportform.tex` does it
   correspond to? Do the preconditions match that theorem's hypotheses?
3. **Check for structure parameters.** If any parameter is a structure,
   name the field(s) that make it non-trivial.
4. **Write 1-2 sentences.** Place immediately before the closing `-/`.

## How the lint enforces it

`scripts/lint_axiom_soundness.sh` runs three checks:

1. **Soundness annotation**: Every `axiom` has `**Soundness:**` in its
   preceding docstring.
2. **Docstring presence**: Every `axiom` has a `/--` docstring within
   40 lines above it.
3. **Inventory sync**: Every source axiom appears in `knownProjectAxioms`
   in `soundness/Main.lean`, and vice versa.

CI runs this script before `lake build`.

## When adding a new axiom

1. Write a `/-- ... -/` docstring with `**Why axiom:**` and `**Soundness:**`.
2. Add the axiom name to `knownProjectAxioms` in `soundness/Main.lean`.
3. Run `bash scripts/lint_axiom_soundness.sh` locally to verify.
4. The CI step will catch any omissions.
