import Incorrectness.VCGen

open Language
open Incorrectness

/-!
# While-Loop Automation Test Suite

Tests for the three new while-automation tactics:

1. `incorrectness_auto_while N`         — explicit bounded unrolling
2. `incorrectness_auto_while_search`    — auto k-search (1..10)
3. `incorrectness_auto_inv (Inv := ...)` — indexed-invariant hint

Each section keeps examples grouped by tactic, with the same triple
sometimes proved by multiple tactics for direct comparison.
-/

-- =============================================================
-- Approach 1: incorrectness_auto_while N (explicit k)
-- =============================================================

/-- W1.1 — 1 iteration, user picks k=1. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 1)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 1) *] := by
  incorrectness_auto_while 1

/-- W1.2 — 2 iterations, user picks k=2. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 2)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 2) *] := by
  incorrectness_auto_while 2

/-- W1.3 — 3 iterations, user picks k=3. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 3)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 3) *] := by
  incorrectness_auto_while 3

/-- W1.4 — Larger bound. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 5)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 5) *] := by
  incorrectness_auto_while 5

-- =============================================================
-- Approach 2: incorrectness_auto_while_search (auto k)
-- =============================================================

/-- W2.1 — Same as W1.1 but no manual k. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 1)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 1) *] := by
  incorrectness_auto_while_search

/-- W2.2 — Same as W1.2 but no manual k. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 2)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 2) *] := by
  incorrectness_auto_while_search

/-- W2.3 — Same as W1.3 but no manual k. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 3)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 3) *] := by
  incorrectness_auto_while_search

/-- W2.4 — Same as W1.4 but no manual k. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 5)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 5) *] := by
  incorrectness_auto_while_search

-- =============================================================
-- Approach 3: incorrectness_auto_inv (invariant hint)
-- =============================================================

/-- W3.1 — Same triple as W1.1 / W2.1, via invariant.
    Compare proof size and form. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 1)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 1) *] := by
  incorrectness_auto_inv (fun i s => s "x" = i ∧ i ≤ 1)

/-- W3.2 — Same triple as W1.3 / W2.3, via invariant. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 3)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 3) *] := by
  incorrectness_auto_inv (fun i s => s "x" = i ∧ i ≤ 3)

/-- W3.3 — **Parametric loop, IMPOSSIBLE with bounded approach.**
    Tests the invariant approach's unique strength. -/
example : [* (fun s => s "x" = 0 ∧ s "n" > 0) *]
          (Stmt.whileDo (fun s => s "x" < s "n")
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = t "n" ∧ t "n" > 0) *] := by
  incorrectness_auto_inv (fun i s => s "x" = i ∧ i ≤ s "n" ∧ s "n" > 0)

-- =============================================================
-- Approach Comparison: same triple via different tactics
-- =============================================================

/-- C1 — `[x=0] while x<3 do x:=x+1 [x=3]`
    via explicit-k (k=3). -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 3)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 3) *] := by
  incorrectness_auto_while 3

/-- C2 — Same triple via auto-search (no k). -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 3)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 3) *] := by
  incorrectness_auto_while_search

/-- C3 — Same triple via invariant. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 3)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 3) *] := by
  incorrectness_auto_inv (fun i s => s "x" = i ∧ i ≤ 3)

-- =============================================================
-- Edge cases & limitations
-- =============================================================

/-- Edge.1 — Empty loop body case: `while x<0 do x:=x+1` from x=0
    should give x=0 (immediate exit). With k=0, just one disjunct. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 0)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 0) *] := by
  incorrectness_auto_while 0

/-- Edge.2 — Same via search. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 0)
                        (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 0) *] := by
  incorrectness_auto_while_search
