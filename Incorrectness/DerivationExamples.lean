import Incorrectness.Derivation
import Incorrectness.VCGen

open Language
open Incorrectness

/-!
# Derivation Tree Examples

These examples demonstrate building explicit syntactic derivation trees
for IL triples using the `Derivation` inductive type.

Each `def` constructs a derivation tree (a proof object), and
the final `example`s apply `soundness` to convert them into
semantic IL triples.
-/

-- ============================================
-- Example 1: Skip (direct axiom)
-- ============================================

/-- Skip preserves any predicate. Simplest possible derivation. -/
def skip_deriv : Derivation (fun s => s "x" = 5) Stmt.skip (fun s => s "x" = 5) :=
  .skip

-- ============================================
-- Example 2: Assignment (exact SP postcondition)
-- ============================================

/-- Assignment where postcondition matches the SP output exactly.
    No consequence needed — just the axiom. -/
def assign_exact_deriv : Derivation (fun s => s "x" = 0)
    (Stmt.assign "x" (fun s => s "x" + 1))
    (fun t => ∃ s, s "x" = 0 ∧ t = s["x" ↦ s "x" + 1]) :=
  .assign

-- ============================================
-- Example 3: Assignment (simplified postcondition)
-- ============================================

/-- Assignment with user-friendly postcondition `x = 1`.
    Uses consequence to weaken from the exact SP output. -/
def assign_simple_deriv : Derivation (fun s => s "x" = 0)
    (Stmt.assign "x" (fun s => s "x" + 1))
    (fun t => t "x" = 1) :=
  .consequence
    (fun _ h => h)
    .assign
    (fun t ht => ⟨t["x" ↦ 0], by simp [State.update], by state_ext⟩)

-- ============================================
-- Example 4: Sequence (x := 1; y := x + 1)
-- ============================================

/-- Two assignments in sequence. The intermediate predicate between
    the two assigns is computed automatically by the assign rule.
    Consequence weakens to the readable postcondition `x=1 ∧ y=2`. -/
def seq_deriv : Derivation (fun _ => True)
    (Stmt.seq
      (Stmt.assign "x" (fun _ => 1))
      (Stmt.assign "y" (fun s => s "x" + 1)))
    (fun t => t "x" = 1 ∧ t "y" = 2) :=
  .consequence
    (fun _ h => h)
    (.seq .assign .assign)
    (fun t ⟨htx, hty⟩ =>
      ⟨t["y" ↦ 0],
       ⟨t["y" ↦ 0]["x" ↦ 0], trivial, by state_ext⟩,
       by state_ext⟩)

-- ============================================
-- Example 5: If-then (under-approximation)
-- ============================================

/-- If-then-else using only the true branch.
    Demonstrates IL's under-approximation: we only claim
    states reachable via one branch. -/
def ite_deriv : Derivation (fun s => s "x" > 0)
    (Stmt.ifThenElse (fun s => s "x" > 0)
      (Stmt.assign "y" (fun _ => 1))
      (Stmt.assign "y" (fun _ => 0)))
    (fun t => t "y" = 1 ∧ t "x" > 0) :=
  .consequence
    (fun _ h => h)
    (.if_then .assign)
    (fun t ⟨hty, htx⟩ =>
      ⟨t["y" ↦ 0],
       ⟨⟨by simp [State.update]; exact htx,
         by simp [State.update]; exact htx⟩,
        by state_ext⟩⟩)

-- ============================================
-- Example 6: Assert error path
-- ============================================

/-- Assert error path: x:=0 then assert(x>0).
    The assertion fails, but the error state x=0 is reachable. -/
def assert_err_deriv : Derivation (fun _ => True)
    (Stmt.seq
      (Stmt.assign "x" (fun _ => 0))
      (Stmt.assert (fun s => s "x" > 0)))
    (fun t => t "x" = 0) :=
  .consequence
    (fun _ h => h)
    (.seq .assign .assert)
    (fun t ht => ⟨t, trivial, by state_ext⟩)

-- ============================================
-- Example 7: inc() from O'Hearn Figure 9
-- ============================================

/-- The inc() procedure: assert(x≥0); x := x+1.
    Derivation: seq of assert (preserves predicate) and assign. -/
def inc_deriv : Derivation (fun s => s "x" ≥ 0)
    (Stmt.seq
      (Stmt.assert (fun s => s "x" ≥ 0))
      (Stmt.assign "x" (fun s => s "x" + 1)))
    (fun t => t "x" > 0) :=
  .consequence
    (fun _ h => h)
    (.seq .assert .assign)
    (fun t ht => ⟨t["x" ↦ t "x" - 1], by simp [State.update], by state_ext⟩)

-- ============================================
-- Example 8: While loop (1 iteration)
-- ============================================

/-- While loop with 1 iteration via the indexed invariant rule.
    Inv(i)(s) = (s "x" = i ∧ i ≤ 1).

    The derivation tree structure:
      consequence
      └─ while_iter
         └─ ∀ i, consequence
                 └─ assign -/
def while_deriv : Derivation (fun s => s "x" = 0)
    (Stmt.whileDo (fun s => s "x" < 1) (Stmt.assign "x" (fun s => s "x" + 1)))
    (fun t => t "x" = 1) :=
  .consequence
    (fun _ ⟨h, _⟩ => h)
    (.while_iter (Inv := fun i s => s "x" = i ∧ i ≤ 1)
      (fun i => .consequence (fun _ h => h) .assign (fun t ⟨htx, hle⟩ => by
        have hi : i = 0 := by omega
        subst hi
        exact ⟨t["x" ↦ 0],
          ⟨⟨by simp [State.update], by omega⟩, by simp [State.update]⟩,
          by state_ext⟩)))
    (fun t ht => ⟨by omega, 1, ht, by omega⟩)

-- ============================================
-- Soundness: Derivation → Semantic Triple
-- ============================================

/-- Every derivation above yields a valid semantic IL triple
    via the soundness meta-theorem. -/

example : [* (fun s => s "x" = 5) *]
    (Stmt.skip)
    [* (fun s => s "x" = 5) *] :=
  soundness skip_deriv

example : [* (fun s => s "x" = 0) *]
    (Stmt.assign "x" (fun s => s "x" + 1))
    [* (fun t => t "x" = 1) *] :=
  soundness assign_simple_deriv

example : [* (fun _ => True) *]
    (Stmt.seq
      (Stmt.assign "x" (fun _ => 1))
      (Stmt.assign "y" (fun s => s "x" + 1)))
    [* (fun t => t "x" = 1 ∧ t "y" = 2) *] :=
  soundness seq_deriv

example : [* (fun s => s "x" ≥ 0) *]
    (Stmt.seq
      (Stmt.assert (fun s => s "x" ≥ 0))
      (Stmt.assign "x" (fun s => s "x" + 1)))
    [* (fun t => t "x" > 0) *] :=
  soundness inc_deriv

example : [* (fun s => s "x" = 0) *]
    (Stmt.whileDo (fun s => s "x" < 1) (Stmt.assign "x" (fun s => s "x" + 1)))
    [* (fun t => t "x" = 1) *] :=
  soundness while_deriv
