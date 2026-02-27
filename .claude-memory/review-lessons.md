# Planning & Review Process Lessons

## Fine-tooth-comb review before merge
- Review mathematical plan docs carefully before merging — errors in plans become wrong theorem statements
- Stage 2 review caught 5 errors: support formula directions, false integrability claim, wrong line refs, wrong dependency graph, wrong definition label
- Fixing a plan doc is cheap; fixing wrong Lean code mid-implementation is expensive

## Preimage direction is subtle
- `dilationOp a g = g ∘ (· / a)` means `supp(U_a g) = a · supp(g)`, NOT `a⁻¹ · supp(g)`
- `translationOp t φ = φ ∘ (· - t)` means `supp(S_t φ) = t + supp(φ)`
- The preimage of `(· / a)` is `(· * a)` but the *image* of support goes the other direction

## archWeight singularity (Stage 2 critical insight)
- w(t) ~ 1/(2t) near t=0 is NOT integrable alone
- The product w(t) * ‖G̃ - S_t G̃‖² IS integrable because ‖G̃ - S_t G̃‖² = O(t²) from translation continuity
- This O(t²) cancellation is the key analytic estimate in the archimedean energy decomposition

## Copilot review patterns
- Multiple review rounds catch real issues (grep portability, scan scope, doc consistency)
- Copilot sometimes flags correct code as wrong (grep logic inversion claim) — verify before changing
- PR description/doc consistency issues are common — keep tables and step counts in sync
- Copilot often takes ~3 minutes but leaves no comments (silent approval) — don't wait indefinitely for feedback that may not come

## Don't defer proofs to sorry
- If a proof is likely within reach (5-10 lines), prove it immediately rather than adding `sorry`
- Sorry stubs create extra commit churn: add sorry → review → close sorry → review again
- Better: take 10 extra minutes to find the right API than add 2 extra review cycles
- Exception: genuinely hard proofs that need separate investigation

## Integrability-first in Lean
- Lean demands integrability proofs BEFORE integral manipulation (integral_add, integral_sub need Integrable hypotheses)
- LaTeX proofs defer convergence justification; Lean cannot
- Front-load integrability lemmas in implementation order so algebraic steps can chain results

## Stage planning structure that works
- Split hard analytic estimates into their own file (ArchimedeanWeight.lean)
- Keep algebraic assembly separate (ArchimedeanDistribution.lean chains results)
- Document corner cases explicitly in plan (Finset construction, measurability, singularity cancellation)
- Create GitHub issues with dependencies/blocking before starting implementation

## Verify Mathlib API names during plan review, not during implementation
- Use `lean_loogle`, `lean_leansearch`, `lean_local_search` MCP tools during plan review
- Mark each API as "✅ Verified" or "manual proof needed" in the plan
- Catches missing lemmas early (e.g. `IsCompact.infDist_compl_pos` doesn't exist)
- Avoids wasted scratch `run_code` blocks during implementation

## Include tests in every PR
- Follow the Stage2Tests.lean pattern: compile-time `example` statements exercising each export
- Don't defer tests to a final batch PR — reviewers need to see tests alongside the code
- Tests also serve as documentation of the file's API surface

## Scope assembly PRs tightly
- PR H (EnergyForm) went cleanly because it stayed at definitions + immediate properties
- The plan correctly identified that a full "assembly theorem" connecting distributions to the energy form would be a rabbit hole (ℂ vs ENNReal type mismatch, no LinearIsometry bridge for dilationOp)
- Better to ship clean definitions + basic properties than attempt a complex theorem and need sorry
- The remark in Definition 3.1 (lamportform.tex lines 446-470) explicitly says downstream arguments only use abstract properties of E_λ — so the assembly connection is not needed for forward progress

## Create the feature branch BEFORE writing code
- Writing code on the wrong branch (e.g. previous PR's branch) forces a stash/switch/pop dance
- Always `git checkout main && git pull && git checkout -b <new-branch>` before touching any files

## Plan-level signatures may have unused parameters
- A plan may include `hLam : 1 < cutoffLambda` in a theorem that doesn't actually need it in the proof
- The LSP `unusedVariables` linter catches this immediately — trust it and remove unused params
- Cleaner API > matching the plan exactly; the plan is a sketch, the compiler is the arbiter

## `let` bindings improve proof readability and line length
- `let T := kato_operator cutoffLambda hLam` then using `T` throughout avoids 100+ char lines
- Better than mechanical line-wrapping of repeated long expressions

## Full workflow (strict ordering)
1. **Plan** — I write, user reviews, I revise
2. **Corner cases** — user asks, I revise
3. **Fine-tooth-comb** — user asks, I revise (verify Mathlib API names, write Lean tactic sketches)
4. **User accepts** the plan
5. **Implement** — no code before step 4
6. **Push + create PR**
7. **Copilot review** — only after PR exists
- User drives the review loop, not me
- Don't push and request Copilot reviews independently
- Steps 1-4 happen before any Lean code is written
- Skipping steps 2-3 causes multiple Copilot review rounds (6A had 3 rounds)

## Search for the most specific Mathlib lemma first
- Before writing a calc chain, search for the exact lemma shape you need (e.g., `lintegral_indicator_one` not `lintegral_indicator` + manual simplification)
- Use `lean_local_search` proactively when you know the shape: "integral of indicator of 1 = measure"
- Composing 3 general lemmas is always worse than finding 1 specific lemma

## Verify interval types before reaching for measure finiteness
- `logInterval L = Ioo (-L) L` (open), NOT `Icc` (closed)
- `measure_Ioo_lt_top` for open intervals, `Real.volume_Icc` + `ENNReal.ofReal_lt_top` for closed
- Getting this wrong wastes an iteration — check the definition first

## LSP needs `lake build` after import graph changes
- Adding a new file + import causes `lean_diagnostic_messages` to return `success: false`
- Fall back to `lake build` for correctness confirmation when imports change

## Always register new files in the root module
- After merging a new `.lean` file, verify the root `ConnesLean.lean` has an `import` for it
- PR #66 (IndicatorEnergy) was merged without adding the import — `lake build ConnesLean` never compiled it
- Fixed in #67 as a separate housekeeping PR
- Checklist: new file created → import added to root → tests import root → CI catches regressions

## Housekeeping fixes as separate PRs
- User prefers root file fixes, import gaps, etc. as their own PRs (not bundled into feature PRs)
- Keeps git history clean: one concern per PR
- Even if the feature PR needs the fix, create the fix PR first, merge it, then rebase the feature branch

## Test helpers in isolation before assembling the full file
- Write each helper theorem via `lean_run_code` first, then assemble into the file
- The first approach (write everything, hope it compiles) produced 15 errors in Stage 6C
- The second approach (validate each piece, then assemble) was much faster
- Especially important when proofs involve ENNReal coercions, set indicator rewrites, or namespace-sensitive names

## Plan verification must match the target file's open declarations
- Plan-phase `lean_run_code` tests often use `import Mathlib` (everything available)
- The actual file only has transitive imports — names may not be in scope
- Plan-phase tests should use the same `open` declarations to catch `Set`/`Finset` ambiguity early
- `lean_run_code` should import the actual dependency (e.g. `import ConnesLean.Stage6.InvarianceSplit`) not `import Mathlib`
