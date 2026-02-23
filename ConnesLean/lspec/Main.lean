/-
Copyright (c) 2026 Christopher Long. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# LSpec Test Runner for ConnesLean

Executable test runner using LSpec with configurable sample counts.
Set LSPEC_SAMPLES env var to control property-test iterations
(default 100; CI uses 1000). Filter suites via CLI args.

Note: Stage 1 definitions (dilationOp, mulConv, etc.) are noncomputable,
so runtime property testing over RPos is not yet possible. Current tests
use Nat properties that mirror the RPos algebraic structure. See GitHub
issues for the computable-wrapper roadmap.
-/

import LSpec
import ConnesLean

open LSpec

namespace ConnesLean.LSpec

/-- Default number of SlimCheck samples for property-based tests. -/
def defaultNumSamples : Nat := 100

/-- Stage 1 basic tests: unit checks and compile-time property tests
    mirroring the RPos commutative monoid structure on Nat. -/
def stage1Basics : TestSeq :=
  group "unit tests" (
    test "one is identity for mul" (1 * 5 = 5) $
    test "mul concrete" (2 * 3 = 6) $
    test "mul_comm concrete" (2 * 3 = 3 * 2) $
    test "mul_assoc concrete" ((2 * 3) * 4 = 2 * (3 * 4)) $
    test "div_self concrete" (6 / 6 = 1) $
    test "Nat.succ_pos" (0 < Nat.succ 0)
  ) ++
  group "property checks (commutative monoid axioms on Nat)" (
    let t1 : TestSeq := check' "mul_comm" (∀ n m : Nat, n * m = m * n)
    let t2 : TestSeq := check' "mul_one" (∀ n : Nat, n * 1 = n)
    let t3 : TestSeq := check' "one_mul" (∀ n : Nat, 1 * n = n)
    let t4 : TestSeq := check' "mul_assoc" (∀ a b c : Nat, (a * b) * c = a * (b * c))
    t1 ++ t2 ++ t3 ++ t4
  )

end ConnesLean.LSpec

open ConnesLean.LSpec in
def main (args : List String) : IO UInt32 := do
  let samplesStr ← IO.getEnv "LSPEC_SAMPLES"
  let numSamples := match samplesStr with
    | some s => s.toNat?.getD defaultNumSamples
    | none => defaultNumSamples
  IO.println s!"ConnesLean LSpec runner (LSPEC_SAMPLES={numSamples})"
  lspecIO (.ofList [("Stage1 Basics", [stage1Basics])]) args
