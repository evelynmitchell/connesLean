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

## Axiom soundness review — "construct the enemy"
- After writing any axiom or structure that encodes a hypothesis, try to construct it for pathological inputs (∅, full set, arbitrary B)
- If the structure can be trivially constructed without providing the key mathematical property, the axiom is too strong
- Fix: fold axiom conclusions into the structure as fields, so constructing it requires proving the property
- Name structures after what they ASSUME, not what they're motivated by (e.g. `EnergyFormSplit` not `SemigroupInvariantIdeal`)
- Add executable soundness tests (not just comments) — Lean `example` proofs that cross-check axiom outputs at degenerate inputs against independently proved facts
- Caught by Copilot review on PR #91 — should have been caught during planning

## Documentation annotations are necessary but not sufficient
- `**Soundness:**` annotations force authors to think about precondition adequacy
- But executable cross-checks (axiom at zero function, empty set, etc.) are cheap and catch real bugs
- Default to writing both — annotation + test — for every axiom

## Shell script linting for Lean projects
- `^axiom ` misses attributed axioms — use `^\s*axiom ` and `--exclude-dir` (not `grep -v`)
- Declaration boundary regex must cover all Lean keywords: axiom, theorem, def, lemma, instance, abbrev, structure, class, noncomputable, private, protected
- When scanning backwards through docstrings, track IN_DOCSTRING state (enter at `-/`, only count markers inside)

## Branch management
- Always check if the current branch already has a PR before trying `gh pr create`
- For independent work, create a fresh branch from main rather than building on an existing PR branch

## Import chain verification
- `lean_local_search` finding a name does NOT mean it's importable — it searches all project files
- `lean_run_code` has all of Mathlib available; your file only has its transitive imports
- Always verify the actual transitive import chain before using a theorem from another file
- LSP needs `lake build` after import graph changes

## Finiteness proofs are cheaper than bound proofs
- When you only need `< ⊤` (not a specific bound), decompose into finite-measure pieces
- Example: `inner_integral_one_lt_top` decomposed as `≤ volume(I) + volume(I+shift) < ⊤`
- This was ~30 lines vs the tight `≤ 2t` bound which was ~50 lines
- Only compute tight bounds when downstream proofs actually need them (e.g., canceling the archWeight `1/t` singularity)

## Prototype ENNReal proofs in lean_run_code first
- ENNReal arithmetic (`ofReal_mul`, `ofReal_le_ofReal`, `mul_le_mul'`, `field_simp`) is where most iteration happens
- The math is usually obvious; making Lean's type system happy is not
- A 5-line `lean_run_code` test saves 3-4 edit-diagnose cycles on the real file

## Don't write helper lemmas for rpow/npow-sensitive goals
- Lean may elaborate `^ (2 : ℝ)` as rpow in one context and `^ 2` as npow in another
- Separate helper lemmas lock in one form; inline case analysis adapts to either
- `simp` handles the rpow↔npow coercion when the cases are simple ({0,1}-valued functions)

## When the first approach to a subgoal gets messy, scrap and simplify
- First attempt at prime inner integral finiteness: `lintegral_indicator` + `measure_union_lt_top` → tangled in preimage notation, failed `rw`
- Scrapped for `inner_integral_one_lt_top` helper: `lintegral_add_right` + `measurePreserving_sub_const` → clean 30 lines
- Cost of persisting with a broken approach > cost of restarting with a simpler one
