import Incorrectness.VCGen

open Language
open Incorrectness

/-!
# incorrectness_auto Test Suite

Testing the automated tactic against all loop-free examples from VCExamples.lean.
-/

-- ============================================
-- Test 1: Skip
-- ============================================
example : [* (fun s => s "x" = 5) *]
          (Stmt.skip)
          [* (fun s => s "x" = 5) *] := by
  incorrectness_auto

-- ============================================
-- Test 2: Assume
-- ============================================
example : [* (fun _ => True) *]
          (Stmt.assume (fun s => s "x" > 0))
          [* (fun s => s "x" > 0) *] := by
  incorrectness_auto

-- ============================================
-- Test 3: Assignment (exact SP postcondition)
-- ============================================
example : [* (fun s => s "x" = 0) *]
          (Stmt.assign "x" (fun s => s "x" + 1))
          [* (fun t => ∃ s, s "x" = 0 ∧ t = s["x" ↦ s "x" + 1]) *] := by
  incorrectness_auto

-- ============================================
-- Test 4: Assignment (simplified postcondition)
-- ============================================
example : [* (fun s => s "x" = 0) *]
          (Stmt.assign "x" (fun s => s "x" + 1))
          [* (fun t => t "x" = 1) *] := by
  incorrectness_auto

-- ============================================
-- Test 5: Sequence (x := 1; y := x + 1)
-- ============================================
example : [* (fun _ => True) *]
          (Stmt.seq
            (Stmt.assign "x" (fun _ => 1))
            (Stmt.assign "y" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 1 ∧ t "y" = 2) *] := by
  incorrectness_auto

-- ============================================
-- Test 6: If-then-else (true branch)
-- ============================================
example : [* (fun s => s "x" > 0) *]
          (Stmt.ifThenElse
            (fun s => s "x" > 0)
            (Stmt.assign "y" (fun _ => 1))
            (Stmt.assign "y" (fun _ => 0)))
          [* (fun t => t "y" = 1 ∧ t "x" > 0) *] := by
  incorrectness_auto

-- ============================================
-- Test 7: inc() — assert + assign
-- ============================================
example : [* (fun s => s "x" ≥ 0) *]
          (Stmt.seq
            (Stmt.assert (fun s => s "x" ≥ 0))
            (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" > 0) *] := by
  incorrectness_auto

-- ============================================
-- Test 8: client() — two inc()s
-- ============================================
example : [* (fun s => s "x" ≥ 0) *]
          (Stmt.seq
            (Stmt.seq
              (Stmt.assert (fun s => s "x" ≥ 0))
              (Stmt.assign "x" (fun s => s "x" + 1)))
            (Stmt.seq
              (Stmt.assert (fun s => s "x" ≥ 0))
              (Stmt.assign "x" (fun s => s "x" + 1))))
          [* (fun t => t "x" > 1) *] := by
  incorrectness_auto

-- ============================================
-- Test 9: test() — full Figure 9
-- ============================================
example : [* (fun _ => True) *]
          (Stmt.seq
            (Stmt.seq
              (Stmt.assign "x" (fun _ => 0))
              (Stmt.seq
                (Stmt.seq
                  (Stmt.assert (fun s => s "x" ≥ 0))
                  (Stmt.assign "x" (fun s => s "x" + 1)))
                (Stmt.seq
                  (Stmt.assert (fun s => s "x" ≥ 0))
                  (Stmt.assign "x" (fun s => s "x" + 1)))))
            (Stmt.assert (fun s => s "x" ≥ 2)))
          [* (fun t => t "x" = 2 ∧ t "x" ≥ 2) *] := by
  incorrectness_auto

-- ============================================
-- Test 10: Assert error path
-- ============================================
example : [* (fun _ => True) *]
          (Stmt.seq
            (Stmt.assign "x" (fun _ => 0))
            (Stmt.assert (fun s => s "x" > 0)))
          [* (fun t => t "x" = 0) *] := by
  incorrectness_auto

-- ============================================
-- Test 11: If-else (right branch)
-- ============================================
example : [* (fun s => s "x" = 3) *]
          (Stmt.ifThenElse
            (fun s => s "x" > 5)
            (Stmt.assign "y" (fun _ => 10))
            (Stmt.assign "y" (fun _ => 20)))
          [* (fun t => t "y" = 20 ∧ t "x" = 3) *] := by
  incorrectness_auto

-- ============================================
-- Test 12: Assume in sequence
-- ============================================
example : [* (fun _ => True) *]
          (Stmt.seq
            (Stmt.assume (fun s => s "x" > 0))
            (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" > 1) *] := by
  incorrectness_auto
