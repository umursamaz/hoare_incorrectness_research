import Incorrectness.VCGen

open Language
open Incorrectness

/-!
# Real-World Bug Detection Examples

This file collects examples that mimic *realistic* bug patterns
found in production code, encoded within our Nat-only state model.
Each example demonstrates that an IL triple of the form
`[precondition] buggy_program [bug_state]` is **provable**, meaning
the bug state is genuinely reachable from the precondition.

In standard usage the user writes a postcondition describing the
*intended* outcome and `incorrectness_auto` proves whether a state
violating that intent is reachable. When the proof succeeds, a bug
exists; when it fails, the bug pattern doesn't manifest in our model.

Each example is closed by a single tactic call (the unified
`incorrectness_auto` dispatcher), which internally tries the
loop-free path first and falls back to bounded while search.

The bug categories covered here:

| # | Category                            | Loop? |
|---|-------------------------------------|-------|
| 1 | `<` vs `≤` in withdrawal check      | no    |
| 2 | `≥` vs `>` in discount threshold    | no    |
| 3 | `>` vs `≥` in age verification      | no    |
| 4 | Logical AND vs OR in access control | no    |
| 5 | Off-by-one: loop-counter starts at 0 | yes  |
| 6 | `≤` vs `<` in loop guard            | yes   |
| 7 | Loop runs one extra time            | yes   |
| 8 | Two-stage validation, second stage skipped | no |
-/

-- =============================================================
-- Example 1 — Bank withdrawal validator: `<` instead of `≤`
-- =============================================================
/-
A banking system *should* allow withdrawal whenever the requested
amount is ≤ balance. The buggy code uses strict `<`, so a request
equal to the balance is incorrectly rejected.

Scenario: balance = 100, withdrawal = 100. The user expects approval,
but the buggy program lands in the rejection branch. This bug state
is reachable, hence provable.
-/
example :
  [* (fun s => s "balance" = 100 ∧ s "withdrawal" = 100) *]
  (Stmt.ifThenElse
    (fun s => s "withdrawal" < s "balance")    -- BUG: should be ≤
    (Stmt.assign "approved" (fun _ => 1))
    (Stmt.assign "approved" (fun _ => 0)))
  [* (fun t => t "approved" = 0 ∧ t "balance" = 100 ∧ t "withdrawal" = 100) *] := by
  incorrectness_auto

-- =============================================================
-- Example 2 — Discount threshold: `≥` instead of `>`
-- =============================================================
/-
The pricing rule says "10% discount for orders over $1000".
A buggy implementation uses `≥`, applying the discount at exactly
$1000 when it shouldn't.

Scenario: amount = 1000. Buggy program applies the discount.
Bug state reachable.
-/
example :
  [* (fun s => s "amount" = 1000) *]
  (Stmt.ifThenElse
    (fun s => s "amount" ≥ 1000)               -- BUG: should be >
    (Stmt.assign "discounted" (fun _ => 1))
    (Stmt.assign "discounted" (fun _ => 0)))
  [* (fun t => t "discounted" = 1 ∧ t "amount" = 1000) *] := by
  incorrectness_auto

-- =============================================================
-- Example 3 — Age verification: `>` instead of `≥`
-- =============================================================
/-
Age gate should permit `age ≥ 18`. Buggy implementation uses strict
`>`, rejecting exactly-18-year-olds.

Scenario: age = 18. Buggy program denies access. Bug reachable.
-/
example :
  [* (fun s => s "age" = 18) *]
  (Stmt.ifThenElse
    (fun s => s "age" > 18)                    -- BUG: should be ≥
    (Stmt.assign "allowed" (fun _ => 1))
    (Stmt.assign "allowed" (fun _ => 0)))
  [* (fun t => t "allowed" = 0 ∧ t "age" = 18) *] := by
  incorrectness_auto

-- =============================================================
-- Example 4 — Access control: AND vs OR confusion
-- =============================================================
/-
A system should grant access only to users who are BOTH admin AND
active. The buggy version uses OR, so any active non-admin user
also gets access.

Scenario: admin = 0, active = 1. Buggy program grants access.
Privilege-escalation bug; reachable.
-/
example :
  [* (fun s => s "admin" = 0 ∧ s "active" = 1) *]
  (Stmt.ifThenElse
    (fun s => s "admin" = 1 ∨ s "active" = 1)  -- BUG: should be ∧
    (Stmt.assign "access" (fun _ => 1))
    (Stmt.assign "access" (fun _ => 0)))
  [* (fun t => t "access" = 1 ∧ t "admin" = 0 ∧ t "active" = 1) *] := by
  incorrectness_auto

-- =============================================================
-- Example 5 — Loop guard: `≤` instead of `<`
-- =============================================================
/-
A loop intended to run exactly 3 times (for x = 0, 1, 2) but the
buggy guard uses `≤ 3` instead of `< 3`, so it runs 4 times.

Final state: x = 4, when the programmer expected x = 3.
Bug reachable via 4 iterations.
-/
example :
  [* (fun s => s "x" = 0) *]
  (Stmt.whileDo
    (fun s => s "x" ≤ 3)                       -- BUG: should be < 3
    (Stmt.assign "x" (fun s => s "x" + 1)))
  [* (fun t => t "x" = 4) *] := by
  incorrectness_auto

-- =============================================================
-- Example 6 — Loop runs one extra iteration (`<` boundary)
-- =============================================================
/-
A loop processes counter from initial value 0 up to (but not
including) some threshold. The intended threshold is 5, but a
buggy off-by-one uses 6, running one extra time.
-/
example :
  [* (fun s => s "counter" = 0) *]
  (Stmt.whileDo
    (fun s => s "counter" < 6)                 -- BUG: intended 5
    (Stmt.assign "counter" (fun s => s "counter" + 1)))
  [* (fun t => t "counter" = 6) *] := by
  incorrectness_auto

-- =============================================================
-- Example 7 — Conditional bug + assignment in sequence
-- =============================================================
/-
A request validator: comparison bug grants access at boundary.
The bug: comparison uses `≥` instead of strict `>`. With input=50
and the threshold also 50, the buggy code proceeds to "approved"
state when it should not.
-/
example :
  [* (fun s => s "input" = 50) *]
  (Stmt.ifThenElse
    (fun s => s "input" ≥ 50)                  -- BUG: intended > 50
    (Stmt.assign "result" (fun _ => 1))        -- approved
    (Stmt.assign "result" (fun _ => 0)))       -- rejected
  [* (fun t => t "result" = 1 ∧ t "input" = 50) *] := by
  incorrectness_auto

-- =============================================================
-- Example 8 — Counter that wraps past intended limit
-- =============================================================
/-
A "rate limiter" intended to permit at most 3 requests but the
buggy guard uses a different threshold, allowing the counter to
exceed the intended cap.
-/
example :
  [* (fun s => s "requests" = 0) *]
  (Stmt.whileDo
    (fun s => s "requests" < 5)                -- BUG: intended 3
    (Stmt.assign "requests" (fun s => s "requests" + 1)))
  [* (fun t => t "requests" = 5) *] := by
  incorrectness_auto

-- =============================================================
-- Example 9 — Sequence of assertions that miss a case
-- =============================================================
/-
A pipeline that asserts intermediate properties. The first assert
catches malformed input. But the assert is too lax: it only checks
`x ≠ 0`, missing the case `x = 1` which the rest of the program
treats specially. After the assert succeeds for x = 1, the program
proceeds to a wrong branch.
-/
example :
  [* (fun s => s "x" = 1) *]
  (Stmt.seq
    (Stmt.assert (fun s => s "x" ≠ 0))         -- assert too weak
    (Stmt.ifThenElse
      (fun s => s "x" > 1)
      (Stmt.assign "result" (fun _ => 100))
      (Stmt.assign "result" (fun _ => 999))))  -- "error sentinel"
  [* (fun t => t "result" = 999 ∧ t "x" = 1) *] := by
  incorrectness_auto

-- =============================================================
-- Example 10 — Nested loops where outer escapes too early
-- =============================================================
/-
An outer loop that's supposed to cover all values but the inner
loop's side effect on the outer counter causes early exit.

Here we encode a single while loop where the body advances `x` by
1, but a second variable `y` should remain 0 — yet the buggy body
also touches `y`. After 2 iterations: x=2, y=2 (not the intended
y=0). The bug: y mutated unintentionally.
-/
example :
  [* (fun s => s "x" = 0 ∧ s "y" = 0) *]
  (Stmt.whileDo
    (fun s => s "x" < 2)
    (Stmt.seq
      (Stmt.assign "x" (fun s => s "x" + 1))
      (Stmt.assign "y" (fun s => s "y" + 1))))   -- BUG: y not supposed to change
  [* (fun t => t "x" = 2 ∧ t "y" = 2) *] := by
  incorrectness_auto
