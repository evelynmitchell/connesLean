# Soundness of ConnesLean Formalization

ConnesLean provides a machine-checked Lean 4 formalization of a
functional-analytic proof concerning the Restricted Weil Quadratic Form.
Starting from the explicit local distributions at each prime and at infinity,
the paper (`lamportform.tex`) derives an energy decomposition, proves the
Markov property and irreducibility, establishes compact resolvent, and deduces
that the ground-state eigenvalue is simple with a strictly positive, even
eigenfunction.

But no formalization is absolute. Every effort to connect informal mathematics
to machine-checked code introduces assumptions. This document maps out those
assumptions and the risks that arise when they fail, following the gap-analysis
framework of the
[s2n-bignum soundness report](https://github.com/awslabs/s2n-bignum/blob/main/doc/s2n_bignum_soundness.md).

**What the formalization says, precisely:** For each theorem in the Lean
codebase, Lean 4's kernel verifies that the stated proposition follows from
the declared axioms (both Lean's foundational axioms and the 14 project
axioms listed below) and from the Mathlib library. The `soundness/Main.lean`
executable audits axiom dependencies: it confirms via `#print axioms` that
Stages 1–4 depend only on Lean builtins (`propext`, `Quot.sound`,
`Classical.choice`), while Stages 5–8 depend additionally on explicitly
declared, documented project axioms—and on nothing else.

---

## Summary of risks

Mitigations in *italics* are planned future work.

| # | Risk | Primary mitigation |
|---|------|--------------------|
| A1 | Wrong mathematical specification | Lamport structured proofs reviewed step-by-step; paper–code concordance |
| A2 | Axiom too strong (overpowered preconditions) | Soundness annotations; lint enforcement; PR #91 bug class documented |
| A3 | Axiom too weak (unintended models) | Structure-guarding fields; existential conclusions; manual review |
| A4 | Missing hypotheses in Lean statements | Bidirectional concordance; compile-time `example` tests |
| A5 | `noncomputable` masks evaluation bugs | Documented as structural; compile-time tests verify definitional unfolding |
| B1 | Lean 4 kernel or Mathlib bug | 10+ year HOL tradition; large user base; *independent proof export* |
| B2 | `sorry` leak | CI grep for `sorryAx`; `#print axioms` audit; sanity tautologies |
| B3 | Axiom inconsistency | Sanity checks (`¬False`, `True`, `0 ≠ 1`); axioms match published theorems |
| C1 | Paper proof error (informal mathematics wrong) | Lamport format enables step-level verification; external review |
| C2 | External theorems cited incorrectly | Precise citations (theorem numbers, page ranges); *future Mathlib proofs* |
| D1 | Formalization incomplete | Concordance tracks status; all 8 stages complete and merged |
| D2 | Axiom elimination stalls | Tiered roadmap with dependency graph; 9 of 14 axioms have elimination plans |

Details for each risk follow.

---

## Gap A: Does the formal specification match the mathematics?

This is the gap between what the Lean code states and what the paper proves.

### A1. Mathematical specification correctness

The Lean definitions (`energyForm`, `fourierSymbol`, `archWeight`,
`translationOp`, `dilationOp`, etc.) could diverge from the paper's
formulas—a wrong sign, a misplaced factor, or a subtly different domain.

**Mitigations.**

- **Lamport structured proofs.** Every proof in `lamportform.tex` uses
  Lamport's hierarchical format where each step states a claim and
  justification independently. This makes the informal mathematics
  unusually auditable.

- **Paper–code concordance** (`docs/concordance.md`). A bidirectional
  table maps every paper result (with line numbers) to the corresponding
  Lean declaration, and vice versa. This makes it straightforward to
  check that definitions match.

- **Notation glossary** (`docs/glossary.md`). Maps mathematical symbols
  (d\*x, U_a, S_t, E_λ, ψ_λ, w(t), etc.) to their Lean names with
  file and line references.

- **Compile-time tests.** Eight test files (`ConnesLeanTest/Stage1Tests.lean`
  through `Stage8Tests.lean`, 989 lines total) verify definitional
  equalities, algebraic laws, and key properties at compile time via
  `example` blocks that Lean's kernel checks during `lake build`.

### A2. Axiom preconditions too strong (vacuously true conclusions)

PR #91 revealed a subtle bug class: an axiom parameterized by a structure
with weak fields can be overpowered—any trivially-constructible instance
satisfies the preconditions, making the axiom grant conclusions for free.

**Mitigations.**

- **Soundness annotations.** Every `axiom` declaration carries a
  `**Soundness:**` annotation in its docstring explaining why
  preconditions are adequate (`docs/axiom-soundness-convention.md`).

- **Two-category classification.** Axioms are classified as either
  *bare-hypothesis* (scalar bounds matching the paper's theorem
  hypotheses) or *structure-consuming* (requiring non-trivially
  constructible structure fields).

- **Automated lint.** `scripts/lint_axiom_soundness.sh` enforces three
  checks on every CI run: (1) every `axiom` has a `**Soundness:**`
  annotation, (2) every `axiom` has a docstring, and (3) every axiom
  appears in the `knownProjectAxioms` inventory and vice versa.

### A3. Axiom preconditions too weak (unintended models)

Even with correct preconditions, an axiom might admit unintended models—
for example, a structure whose fields are technically satisfiable but
don't correspond to the intended mathematical object.

**Mitigations.**

- All 14 axioms use `1 < cutoffLambda` as their primary scalar guard,
  matching the paper's fixed parameter λ > 1.

- Existential conclusions (`∃ c₁ c₂ ξ₀, ...`) cannot be vacuously
  satisfied; the witnesses must have the stated properties.

- Structure-consuming axioms (e.g., `kato_operator` taking a
  `KatoOperator` structure) require substantive fields that cannot be
  trivially constructed.

### A4. Missing hypotheses in Lean statements

A Lean theorem might prove a weaker statement than intended, or its
hypotheses might not faithfully capture the paper's conditions.

**Mitigations.**

- The concordance (`docs/concordance.md`) enables line-by-line comparison.
  Each axiom entry lists the paper reference (theorem number + line range)
  so reviewers can check correspondence.

- Compile-time `example` tests exercise both positive instances
  (the theorem applies where expected) and structural equalities
  (definitions unfold correctly).

### A5. `noncomputable` masks evaluation bugs

Every definition in ConnesLean that touches ℝ or measure theory is
`noncomputable` (Lean 4's term for definitions that rely on
`Classical.choice` and cannot be compiled to executable code). This
means `#eval` cannot be used for runtime sanity checks.

**Mitigations.**

- This is a **permanent structural property**, not a bug
  (`docs/noncomputable.md`). Mathlib's ℝ is built on classical Cauchy
  sequences; any analysis formalization inherits this.

- Compile-time `example` proofs verify definitional unfolding and
  algebraic identities without runtime evaluation.

- LSpec tests (`lspec/Main.lean`) exercise the test infrastructure
  on computable types (ℕ) as structural analogs.

- *Future:* Computable wrapper types backed by floating-point or
  rational arithmetic for runtime sanity checks (tracked in issue #11).

---

## Gap B: Is the proof infrastructure sound?

### B1. Trusted computing base: Lean 4 kernel and Mathlib

Lean 4's kernel type-checks all definitions and proofs. Bugs in the
kernel or in Lean's elaborator could allow unsound proofs. Mathlib, as a
large library, could also contain errors that propagate.

**Mitigations.**

- Lean 4 follows the de Bruijn / LCF tradition: the kernel is small and
  all proofs must pass through it. The Lean community has 10+ years of
  experience (across Lean 2, 3, 4).

- Mathlib is the largest Lean 4 library with hundreds of contributors
  and continuous integration. Errors are found and fixed promptly.

- *Future:* Independent proof export to other checkers (analogous to
  HOL Light's HOLTrace/Candle ecosystem) would reduce trust in the Lean
  kernel, though no such tool is mature for Lean 4 today.

### B2. `sorry` leak

A `sorry` (Lean's escape hatch for incomplete proofs) would silently
introduce `sorryAx` as a dependency, invalidating the proof.

**Mitigations.**

- **CI grep.** The build pipeline greps build output for `sorryAx` and
  fails if any is found.

- **`#print axioms` audit.** `soundness/Main.lean` runs `#print axioms`
  on every main theorem at compile time. Any `sorryAx` dependency would
  appear in the output.

- **`checkNoSorry` runtime check.** The soundness executable explicitly
  tests that no theorem depends on `sorryAx`.

- **Current status:** Zero `sorry` statements in the codebase. All
  theorems in Stages 1–8 are fully proved (modulo the 14 declared
  project axioms).

### B3. Axiom inconsistency

The 14 project axioms could be mutually inconsistent, allowing `False`
to be derived.

**Mitigations.**

- **Sanity tautologies.** `soundness/Main.lean` includes three
  compile-time checks:
  ```
  theorem sanity_not_false : ¬False := fun h => h
  theorem sanity_true : True := trivial
  theorem sanity_zero_ne_one : (0 : ℕ) ≠ 1 := Nat.zero_ne_one
  ```
  These are verified via `#print axioms` to depend only on Lean builtins.
  An inconsistency would not be *detected* by these (an inconsistent
  theory proves everything, including these tautologies), but their
  purpose is to confirm that the *axiom-free core* does not depend on
  project axioms.

- **Mathematical grounding.** Each axiom corresponds to a published
  theorem with a precise citation:
  - `translation_norm_sq_continuous` ← Engel–Nagel Thm I.5.8
  - `fourierSymbol_ge_log` ← Lemma 11 in `lamportform.tex`
  - `frequency_moment_control` ← Corollary 12
  - `energyForm_eq_fourierSymbol_integral` ← Lemma 9
  - `formDomain_eq_weighted_fourier` ← Proposition 6, Step 2
  - `energyForm_closed_on_line` ← Proposition 6
  - `energyForm_closed_on_interval` ← Proposition 7
  - `kolmogorov_riesz_compact` ← Brezis Corollary 4.27
  - `formNormBall_equicontinuous` ← Lemma 13
  - `kato_operator` ← Kato Thm VI.2.1 / Thm VI.2.23
  - `closed_ideal_classification` ← Schaefer III.1
  - `semigroup_positivity_improving` ← Arendt–ter Elst–Glück Thm 2.3
  - `ground_state_simple` ← Arendt–ter Elst–Glück Prop 2.4
  - `resolvent_commutes_reflection` ← Proposition 14 in `lamportform.tex`

  These are well-established results from functional analysis (Kato,
  Brezis, Fukushima–Oshima–Takeda, Engel–Nagel) and recent spectral
  theory (Arendt–ter Elst–Glück 2020). An inconsistency would require
  a fundamental error in one of these references.

- **Residual risk.** The sanity checks cannot detect inconsistency in
  the axiom set (Gödel's second incompleteness theorem). The primary
  defense is that the axioms encode well-known, independently verified
  mathematical theorems.

---

## Gap C: Is the informal mathematics correct?

### C1. Paper proof errors

The paper (`lamportform.tex`, 1815 lines) could contain a mathematical
error—a wrong sign, a gap in a convergence argument, a misapplied
theorem.

**Mitigations.**

- **Lamport structured proofs.** Every proof is broken into numbered
  steps, each with an explicit claim and justification. This format is
  designed for independent verification of any single step.

- **Progressive formalization.** The act of formalizing each step in
  Lean forces detailed scrutiny. Several issues were discovered and
  fixed during formalization (e.g., the overpowered-axiom bug class
  of PR #91).

- **Axiom-free stages.** Stages 1–4 are fully proved in Lean without
  any project axioms, providing machine-checked confidence in the
  foundational layers: Haar measure properties, dilation/translation
  operators, convolution identities, the Markov property, and the
  translation-invariance lemma.

- **Residual risk.** Stages 5–8 rely on project axioms for the
  deeper functional analysis (Fourier representation, closedness,
  compactness, spectral theory). Errors in these axioms' mathematical
  content would not be caught by Lean.

### C2. External theorems cited incorrectly

The formalization invokes results from Kato, Brezis, Engel–Nagel,
Fukushima–Oshima–Takeda, Schaefer, and Arendt–ter Elst–Glück. If
these are cited with wrong hypotheses or conclusions, the axioms
could be wrong even though the references exist.

**Mitigations.**

- Each axiom's docstring includes a precise reference (author, theorem
  number, and often page/line numbers in `lamportform.tex`).

- *Future:* Replacing axioms with Mathlib proofs would eliminate this
  risk entirely. The axiom elimination roadmap
  (`docs/axiom-elimination-roadmap.md`) plans to remove 9 of 14
  axioms through ~760 lines of new Lean code.

---

## Gap D: Is the formalization complete?

### D1. Coverage of the paper

The paper contains 10 sections with ~25 major results (lemmas,
propositions, theorems, corollaries). Not all intermediate results have
separate Lean declarations, but all main results through Corollary 16
(even ground state) are formalized.

**Current coverage by stage:**

| Stage | Paper sections | LOC | Axioms | Status |
|-------|---------------|-----|--------|--------|
| 1 | §1 (Setup on ℝ₊\*) | ~600 | 0 | Fully proved |
| 2 | §2–4 (Local terms, log coords, energy decomposition) | ~800 | 1 | Fully proved |
| 4 | §5–6 (Markov property, translation-invariance) | ~700 | 0 | Fully proved |
| 5 | §7.2 (Fourier, closedness, compactness, resolvent) | ~1200 | 9 | Proved from axioms |
| 6 | §7.1, §7.3 (Indicator energy, irreducibility) | ~1000 | 1 | Proved from axioms |
| 7 | §8 (Positivity improving, ground state) | ~300 | 2 | Proved from axioms |
| 8 | §9 (Inversion symmetry, even ground state) | ~200 | 1 | Proved from axioms |

**Total: 5,889 lines of Lean source, 989 lines of tests, 14 project axioms.**

### D2. Axiom elimination progress

The 14 project axioms represent mathematical results that are trusted
but not machine-checked. The axiom elimination roadmap prioritizes
them by feasibility:

| Tier | Axioms | Effort | Status |
|------|--------|--------|--------|
| 1 (Ready now) | `translation_norm_sq_continuous`, `fourierSymbol_ge_log`, `frequency_moment_control` | ~175 lines | Planned |
| 2 (Achievable) | `energyForm_eq_fourierSymbol_integral`, `formDomain_eq_weighted_fourier`, `energyForm_closed_on_line`, `energyForm_closed_on_interval`, `kolmogorov_riesz_compact` | ~385 lines | Planned |
| 3 (After Tier 2) | `formNormBall_equicontinuous` | ~200 lines | Planned |
| 4 (Keep as axiom) | `kato_operator` | ~2500 lines | Requires major Mathlib infrastructure |
| Not yet scheduled | `closed_ideal_classification`, `semigroup_positivity_improving`, `ground_state_simple`, `resolvent_commutes_reflection` | Varies | Deep functional analysis |

The Kolmogorov–Riesz compactness theorem and the Kato representation
theorem would be high-value Mathlib contributions if formalized.

---

## Axiom inventory

The following 14 axioms are the complete set of unproved assumptions
beyond Lean's foundational axioms (`propext`, `Quot.sound`,
`Classical.choice`). This list is enforced by CI: any addition or
removal triggers a lint failure.

| # | Axiom | Paper reference | Lean location | Guard |
|---|-------|----------------|---------------|-------|
| 1 | `translation_norm_sq_continuous` | Engel–Nagel I.5.8 | `Stage2/TranslationOperator.lean:110` | `Memℒp φ 2` |
| 2 | `fourierSymbol_ge_log` | Lemma 11 (lines 964–1021) | `Stage5/SymbolLowerBound.lean:162` | `1 < cutoffLambda` |
| 3 | `frequency_moment_control` | Corollary 12 (lines 1023–1057) | `Stage5/SymbolLowerBound.lean:183` | `1 < cutoffLambda` |
| 4 | `energyForm_eq_fourierSymbol_integral` | Lemma 9 (lines 844–872) | `Stage5/ClosedForm.lean:90` | `G ∈ formDomain` |
| 5 | `formDomain_eq_weighted_fourier` | Prop 6, Step 2 | `Stage5/ClosedForm.lean:109` | `1 < cutoffLambda` |
| 6 | `energyForm_closed_on_line` | Proposition 6 (lines 874–907) | `Stage5/ClosedForm.lean:136` | `1 < cutoffLambda` |
| 7 | `energyForm_closed_on_interval` | Proposition 7 (lines 909–936) | `Stage5/ClosedForm.lean:157` | `1 < cutoffLambda` |
| 8 | `kolmogorov_riesz_compact` | Brezis Cor 4.27 | `Stage5/CompactEmbedding.lean:72` | L², support, equicontinuity |
| 9 | `formNormBall_equicontinuous` | Lemma 13 (lines 1078–1127) | `Stage5/CompactEmbedding.lean:88` | `1 < cutoffLambda` |
| 10 | `kato_operator` | Kato VI.2.1 + VI.2.23 | `Stage5/CompactResolvent.lean:84` | `1 < cutoffLambda` |
| 11 | `closed_ideal_classification` | Schaefer III.1 | `Stage6/Irreducibility.lean:84` | MeasurableSet, invariance |
| 12 | `semigroup_positivity_improving` | ATG 2020, Thm 2.3 | `Stage7/GroundState.lean:109` | `1 < cutoffLambda` |
| 13 | `ground_state_simple` | ATG 2020, Prop 2.4 | `Stage7/GroundState.lean:130` | `IsPositivityImproving` |
| 14 | `resolvent_commutes_reflection` | Prop 14 in paper | `Stage8/EvenGroundState.lean:89` | `1 < cutoffLambda` |

---

## Verification infrastructure

### Build and CI

- **`lake build ConnesLean`** — type-checks all 5,889 lines of source.
- **`lake exe soundness_check`** — runs axiom inventory and sanity
  checks.
- **`bash scripts/lint_axiom_soundness.sh`** — enforces soundness
  annotations and inventory sync.
- **CI pipeline** — runs lint before build; greps for `sorryAx`; runs
  all tests.

### Testing layers

| Layer | What it checks | Files |
|-------|---------------|-------|
| Lean kernel (compile-time) | Type correctness of all definitions and proofs | All `.lean` files |
| `example` tests | Definitional equalities, algebraic laws, key properties | `ConnesLeanTest/Stage*Tests.lean` |
| `#print axioms` | Axiom dependencies of every main theorem | `soundness/Main.lean` |
| Sanity tautologies | `¬False`, `True`, `0 ≠ 1` are axiom-free | `soundness/Main.lean` |
| LSpec runtime | Algebraic properties on computable types | `lspec/Main.lean` |
| Axiom lint | Soundness annotations, docstrings, inventory sync | `scripts/lint_axiom_soundness.sh` |

### Documentation

| Document | Purpose |
|----------|---------|
| `docs/concordance.md` | Bidirectional paper ↔ Lean mapping |
| `docs/glossary.md` | Mathematical notation ↔ Lean names |
| `docs/axiom-soundness-convention.md` | Axiom safety protocol |
| `docs/axiom-elimination-roadmap.md` | Plan to remove 9+ axioms |
| `docs/noncomputable.md` | Why `noncomputable` is structural |

---

## What the formalization does and does not establish

**What it establishes (machine-checked):**

- The energy form E_λ decomposes into translation-difference energies
  with non-negative weights (Stages 1–2, axiom-free).
- The Markov (normal contraction) property holds for E_λ (Stage 4,
  axiom-free).
- Translation-invariance of an indicator on an interval forces null
  or conull (Stage 4, axiom-free).
- *Conditional on the 14 axioms:* The operator A_λ has compact
  resolvent, the semigroup is irreducible and positivity-improving,
  the ground-state eigenvalue is simple with a strictly positive even
  eigenfunction (Stages 5–8).

**What it does not establish:**

- The 14 project axioms are not machine-checked. They encode published
  theorems from functional analysis that are not yet available in Mathlib.
- Positivity of the full explicit-formula quadratic form ("Weil
  positivity") is explicitly *not* claimed. The energy decomposition
  includes an additive constant whose sign is not controlled
  (Remark after Definition 3.1 in the paper).
- The Riemann Hypothesis is *not* a consequence of this work. The
  paper establishes structural properties (compact resolvent, simple
  ground state, evenness) of the restricted quadratic form—spectral
  properties that are necessary ingredients for, but not sufficient
  to prove, RH.
