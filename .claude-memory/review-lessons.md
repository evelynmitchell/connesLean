# Planning & Review Process Lessons

## Fine-tooth-comb review before merge
- Review mathematical plan docs carefully before merging — errors in plans become wrong theorem statements
- Fixing a plan doc is cheap; fixing wrong Lean code mid-implementation is expensive

## Preimage direction is subtle
- `dilationOp a g = g ∘ (· / a)` means `supp(U_a g) = a · supp(g)`, NOT `a⁻¹ · supp(g)`
- `translationOp t φ = φ ∘ (· - t)` means `supp(S_t φ) = t + supp(φ)`

## archWeight singularity (critical insight)
- w(t) ~ 1/(2t) near t=0 is NOT integrable alone
- The product w(t) * ‖G̃ - S_t G̃‖² IS integrable because ‖G̃ - S_t G̃‖² = O(t²)

## Copilot review patterns
- Copilot sometimes flags correct code as wrong — verify before changing
- Copilot often takes ~3 minutes but leaves no comments (silent approval)

## Integrability-first in Lean
- Lean demands integrability proofs BEFORE integral manipulation
- LaTeX proofs defer convergence justification; Lean cannot
- Front-load integrability lemmas so algebraic steps can chain results

## Stage planning structure that works
- Split hard analytic estimates into their own file (e.g. ArchimedeanWeight.lean)
- Keep algebraic assembly separate (chain results from estimate files)
- Document corner cases explicitly in plan
- Create GitHub issues with dependencies/blocking before starting implementation

## Verify Mathlib API names during plan review, not during implementation
- Use `lean_loogle`, `lean_leansearch`, `lean_local_search` MCP tools during plan review
- Mark each API as "verified" or "manual proof needed" in the plan
- Catches missing lemmas early; avoids wasted scratch blocks during implementation

## Include tests in every PR
- Follow the compile-time `example` pattern exercising each export
- Tests also serve as documentation of the file's API surface

## Scope assembly PRs tightly
- Ship clean definitions + basic properties rather than attempt complex assembly theorems with sorry

## Full workflow (strict ordering)
1. **Plan** — I write, user reviews, I revise
2. **Corner cases** — user asks, I revise
3. **Fine-tooth-comb** — user asks, I revise (verify Mathlib API names)
4. **User accepts** the plan
5. **Implement** — no code before step 4
6. **Push + create PR**
7. **Copilot review** — only after PR exists

## Always register new files in the root module
- After merging a new `.lean` file, verify `ConnesLean.lean` has an `import` for it
- Checklist: new file created → import added to root → tests import root → CI catches regressions

## Housekeeping fixes as separate PRs
- Root file fixes, import gaps, etc. as their own PRs (not bundled into feature PRs)

## Test helpers in isolation before assembling the full file
- Write each helper theorem via `lean_run_code` first, then assemble
- Especially important for ENNReal coercions, set indicator rewrites, namespace-sensitive names

## Plan verification must match the target file's open declarations
- Plan-phase `lean_run_code` should import the actual dependency, not `import Mathlib`
- Match `open` declarations to catch `Set`/`Finset` ambiguity early

## Import chain verification
- `lean_local_search` finding a name does NOT mean it's importable — it searches all project files
- `lean_run_code` has all of Mathlib available; your file only has its transitive imports
- Always verify the actual transitive import chain before using a theorem from another file
- LSP needs `lake build` after import graph changes
