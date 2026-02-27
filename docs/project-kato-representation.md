# Project: Kato Representation Theorem — `kato_operator`

## Goal

Replace the axiom `kato_operator` in
`ConnesLean/ConnesLean/Stage5/CompactResolvent.lean` with a fully proved
theorem. This is the most ambitious axiom in the project — the Kato
representation theorem is a cornerstone of unbounded operator theory.

## Current Axiom

```lean
axiom kato_operator (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda) :
    KatoOperator cutoffLambda
```

`KatoOperator cutoffLambda` packages:
- An unbounded self-adjoint operator `A_λ ≥ 0` on `L²(I)`
- The form identity: `E_λ(G) = ⟨A_λ^{1/2} G, A_λ^{1/2} G⟩` for `G ∈ D(E_λ)`
- The resolvent `(A_λ + α)⁻¹` is a bounded operator for `α > 0`

## Mathematical Source

Kato, *Perturbation Theory for Linear Operators*, Theorem VI.2.1:

> Let `(E, D(E))` be a closed, densely defined, nonnegative, symmetric
> sesquilinear form on a Hilbert space `H`. Then there exists a unique
> self-adjoint operator `A ≥ 0` such that `D(A^{1/2}) = D(E)` and
> `E(u, v) = ⟨A^{1/2} u, A^{1/2} v⟩`.

Also: Reed-Simon, *Methods of Modern Mathematical Physics I*, Theorem VIII.15.

Reference in `lamportform.tex`: Theorem 9, Step 1 (lines 1164–1174).

## Why This Is the Hardest Axiom

The Kato representation theorem requires the following infrastructure,
**none of which exists in Mathlib**:

1. **Unbounded operators on Hilbert spaces** — Mathlib has bounded operators
   (`ContinuousLinearMap`) but not unbounded ones with domains.

2. **Self-adjointness for unbounded operators** — Mathlib has `IsSelfAdjoint`
   for bounded operators. The unbounded version requires careful domain
   management (`A = A*` where domains must match).

3. **Sesquilinear forms with domains** — Mathlib has `SesquilinearForm` but
   not the closed/closable form theory.

4. **Spectral theorem for unbounded self-adjoint operators** — Needed for
   `A^{1/2}` (Borel functional calculus). Mathlib has spectral theory for
   bounded normal operators only.

5. **Friedrichs extension** — The standard proof of Kato's theorem goes
   through the Friedrichs extension of a semibounded symmetric operator.

## Estimated Effort

This is a **major Mathlib infrastructure project**, not a patch:

| Component | Estimated Lines | Difficulty |
|---|---|---|
| Unbounded operator framework | ~500 | Very Hard |
| Unbounded self-adjointness | ~300 | Very Hard |
| Closed form theory | ~200 | Hard |
| Friedrichs extension | ~300 | Very Hard |
| Kato representation theorem | ~200 | Hard |
| Spectral theorem (unbounded) | ~1000+ | Extreme |
| **Total** | **~2500+** | |

## Recommendation: Keep as Axiom

**This axiom should remain an axiom** for the foreseeable future.

Justification:
- The infrastructure gap is enormous (~2500+ lines of new Mathlib code)
- Multiple PhD-level Mathlib projects would need to complete first
- The axiom is clean, well-documented, and references standard texts
- Formalizing Kato is a multi-month project for an experienced Lean contributor

## Partial Progress Paths

If someone wanted to make incremental progress:

### Path 1: Unbounded Operator Framework

Build the foundation that everyone needs:

```lean
structure UnboundedOperator (H : Type*) [InnerProductSpace ℂ H] where
  domain : Submodule ℂ H
  toFun : domain → H

def IsDenselyDefined (A : UnboundedOperator H) : Prop :=
  A.domain.topologicalClosure = ⊤

def adjointDomain (A : UnboundedOperator H) : Submodule ℂ H := ...
def adjoint (A : UnboundedOperator H) : UnboundedOperator H := ...

def IsSelfAdjointUnbounded (A : UnboundedOperator H) : Prop :=
  A.domain = A.adjointDomain ∧ ∀ x ∈ A.domain, A.toFun x = A.adjoint.toFun x
```

**Effort:** ~500 lines. **Mathlib impact:** High — unblocks many projects.

### Path 2: Closed Forms Without Spectral Theory

For our specific use case, we don't need the full spectral theorem. We need:
- Existence of a self-adjoint operator from a closed form
- The resolvent `(A + α)⁻¹` exists as a bounded operator

The Lax-Milgram theorem (which IS closer to Mathlib's reach) gives the
resolvent directly from the form, without going through the spectral theorem:

For `α > 0` and `f ∈ H`, the functional `v ↦ ⟨f, v⟩` is bounded on
`D(E)` equipped with the graph norm `E(v,v) + α‖v‖²`. By Riesz representation,
there exists unique `u ∈ D(E)` with `E(u,v) + α⟨u,v⟩ = ⟨f,v⟩` for all
`v ∈ D(E)`. Set `(A+α)⁻¹ f = u`.

**Effort:** ~400 lines. **Advantage:** Avoids spectral theory entirely.

### Path 3: Accept Weaker Statement

Instead of the full Kato structure, axiomatize only what downstream proofs
actually use:

```lean
-- Just the resolvent, not the full operator
axiom resolvent_exists (cutoffLambda : ℝ) (hLam : 1 < cutoffLambda)
    (α : ℝ) (hα : 0 < α) :
    ∃ R : L²(I) →L[ℂ] L²(I), ∀ G ∈ formDomain cutoffLambda, ∀ v,
      energyForm_sesq cutoffLambda (R G) v + α * inner (R G) v = inner G v
```

This is weaker but sufficient for downstream use and more realistic to prove
(via Lax-Milgram).

## Files to Create/Modify (if attempted)

- **New:** `Mathlib.Analysis.InnerProductSpace.UnboundedOperator` (framework)
- **New:** `Mathlib.Analysis.InnerProductSpace.ClosedForm` (form theory)
- **New:** `Mathlib.Analysis.InnerProductSpace.FriedrichsExtension` (construction)
- **Modify:** `Stage5/CompactResolvent.lean` — replace axiom

## Mathlib Contribution Potential

**Extremely High.** An unbounded operator framework for Mathlib is one of the
most-requested pieces of missing infrastructure. It would unblock:
- Quantum mechanics formalization (Schrödinger operators)
- PDE theory (elliptic regulators, heat equation)
- Spectral geometry (Laplacian on manifolds)
- This project and many others

Multiple Mathlib contributors have expressed interest but the project remains
unstarted as of early 2026.

## Success Criteria

If keeping as axiom (recommended):
- Axiom is well-documented with precise references
- `KatoOperator` structure captures exactly what's needed
- Downstream proofs use only the structure fields, not internal details

If proving (ambitious):
- `kato_operator` is a `theorem`, not an `axiom`
- `lean_verify` shows only standard axioms
- New infrastructure is PR-ready for Mathlib upstream
