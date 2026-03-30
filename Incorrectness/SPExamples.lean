import Incorrectness.SP

open Language
open Incorrectness

/-!
# SP-Based VC Generation Examples

These examples demonstrate the forward SP-based verification condition
approach for Incorrectness Logic.

**Testing strategy:** Each example proves an IL triple using `vc_sound`.
If the proof goes through, it confirms:
1. sp correctly computes reachable states
2. sp_sound correctly connects sp to IL validity
3. The VC approach works end-to-end

**Comparison with manual proofs:** These same triples could be proved
using the existing inference rules (assign_intro, etc.) directly.
The VC approach automates the rule selection — the user only proves
one mathematical formula (the VC), not the program logic derivation.
-/

-- ============================================
-- Example 1: Skip (trivial baseline)
-- ============================================

/-- Skip preserves any predicate.
  VC: (s "x" = 5) → (s "x" = 5)  — trivially true -/
example : [* (fun s => s "x" = 5) *]
          (Stmt.skip)
          [* (fun s => s "x" = 5) *] := by
  apply vc_sound
  intro t ht
  -- Goal: sp Stmt.skip (fun s => s "x" = 5) t
  -- sp skip p = p, so goal is just: t "x" = 5
  exact ht

-- ============================================
-- Example 2: Assume (filters states by condition)
-- ============================================

/-- Assume filters the precondition by the assumed condition.
  VC: (s "x" > 0) → (True ∧ s "x" > 0)  — trivially true -/
example : [* (fun _ => True) *]
          (Stmt.assume (fun s => s "x" > 0))
          [* (fun s => s "x" > 0) *] := by
  apply vc_sound
  intro t ht
  -- Goal: sp (assume ...) (fun _ => True) t
  -- sp (assume B) p = fun s => p s ∧ B s
  -- So goal: True ∧ t "x" > 0
  exact ⟨trivial, ht⟩

-- ============================================
-- Example 3: Assignment (q = sp, identity VC)
-- ============================================

/-- Assignment where postcondition equals the sp output.
  This shows the mechanism works: when q IS sp(c,p), the VC is trivial.
  VC: q t → q t  — identity -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.assign "x" (fun s => s "x" + 1))
          [* (fun t => ∃ s, s "x" = 0 ∧ t = s["x" ↦ s "x" + 1]) *] := by
  apply vc_sound
  intro t ht
  exact ht

-- ============================================
-- Example 4: Assignment (simplified postcondition)
-- ============================================

/-- Assignment with a user-friendly postcondition.
  Program: x := x + 1, precondition: x = 0, expected result: x = 1

  VC: (t "x" = 1) → ∃ s, s "x" = 0 ∧ t = s["x" ↦ s "x" + 1]

  The proof constructs the witness s = t["x" ↦ 0]:
  - s "x" = 0  ✓
  - t = s["x" ↦ 0 + 1] = s["x" ↦ 1]  ✓ (since t "x" = 1) -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.assign "x" (fun s => s "x" + 1))
          [* (fun t => t "x" = 1) *] := by
  apply vc_sound
  intro t ht
  -- ht : t "x" = 1
  -- Goal: ∃ s, s "x" = 0 ∧ t = s["x" ↦ s "x" + 1]
  refine ⟨t["x" ↦ 0], ?_, ?_⟩
  · -- (t["x" ↦ 0]) "x" = 0
    simp [State.update]
  · -- t = (t["x" ↦ 0])["x" ↦ (t["x" ↦ 0]) "x" + 1]
    funext y
    unfold State.update
    by_cases hy : y = "x" <;> simp [hy, ht]

-- ============================================
-- Example 5: Sequence of two assignments
-- ============================================

/-- Two assignments in sequence: x := 1; y := x + 1
  Precondition: True
  Expected result: x = 1 ∧ y = 2

  sp computes forward through both assignments:
  sp(x:=1, True) = ∃ s, True ∧ t = s["x" ↦ 1]
  sp(y:=x+1, above) = ∃ mid, (∃ s, True ∧ mid = s["x" ↦ 1]) ∧ t = mid["y" ↦ mid "x" + 1]
-/
example : [* (fun _ => True) *]
          (Stmt.seq
            (Stmt.assign "x" (fun _ => 1))
            (Stmt.assign "y" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 1 ∧ t "y" = 2) *] := by
  apply vc_sound
  intro t ⟨htx, hty⟩
  -- Goal: sp of the sequence applied to True, evaluated at t
  -- Unfolds to: ∃ mid, (∃ s, True ∧ mid = s["x" ↦ 1]) ∧ t = mid["y" ↦ mid "x" + 1]
  simp only [sp_seq', sp_assign']
  -- Witness for mid: t["y" ↦ 0] (any value for y works since we'll overwrite it)
  -- Actually, let's use a specific mid where x=1 and y has some value
  -- mid = t["y" ↦ 0] means mid "x" = t "x" = 1
  refine ⟨t["y" ↦ 0], ?_, ?_⟩
  · -- ∃ s, True ∧ t["y" ↦ 0] = s["x" ↦ 1]
    -- Witness: s = t["y" ↦ 0]["x" ↦ 0] (any value for x before assignment)
    refine ⟨t["y" ↦ 0]["x" ↦ 0], trivial, ?_⟩
    funext y
    unfold State.update
    by_cases hy : y = "x" <;> simp [hy, htx]
  · -- t = (t["y" ↦ 0])["y" ↦ (t["y" ↦ 0]) "x" + 1]
    funext y
    unfold State.update
    by_cases hy : y = "y" <;> simp [hy, htx, hty]

-- ============================================
-- Example 6: If-then-else
-- ============================================

/-- Conditional: if x > 0 then y := 1 else y := 0
  Precondition: True
  Postcondition: y = 1 (only the true branch)

  This demonstrates under-approximation: we only claim
  the true branch's result. The false branch is "forgotten"
  (disjunct dropping — sound in IL!) -/
example : [* (fun s => s "x" > 0) *]
          (Stmt.ifThenElse
            (fun s => s "x" > 0)
            (Stmt.assign "y" (fun _ => 1))
            (Stmt.assign "y" (fun _ => 0)))
          [* (fun t => t "y" = 1 ∧ t "x" > 0) *] := by
  apply vc_sound
  intro t ⟨hty, htx⟩
  -- Goal: sp of if-then-else
  simp only [sp_ite', sp_assign']
  -- Choose the true branch (left disjunct)
  left
  -- Goal: ∃ s, (s "x" > 0 ∧ s "x" > 0) ∧ t = s["y" ↦ 1]
  refine ⟨t["y" ↦ 0], ⟨?_, ?_⟩, ?_⟩
  · -- precondition: (t["y" ↦ 0]) "x" > 0
    unfold State.update; simp; exact htx
  · -- branch condition: (t["y" ↦ 0]) "x" > 0
    unfold State.update; simp; exact htx
  · -- t = (t["y" ↦ 0])["y" ↦ 1]
    funext y
    unfold State.update
    by_cases hy : y = "y" <;> simp [hy, hty]

-- ============================================
-- Example 7: While loop (1 iteration)
-- ============================================

/-- Simple while loop: while (x < 1) do x := x + 1
  Precondition: x = 0
  Postcondition: x = 1

  We use vc_while_sound with 1 unrolling.
  unroll_while (x < 1) (x := x + 1) 1
    = if (x < 1) then (x := x + 1; assume(¬(x < 1))) else skip

  Since x = 0 < 1, we take the true branch:
    x := x + 1 gives x = 1, then assume(¬(1 < 1)) succeeds. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 1) (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 1) *] := by
  apply vc_while_sound (k := 1)
  intro t ht
  -- ht : t "x" = 1
  -- Goal: sp (unroll_while ...) (fun s => s "x" = 0) t
  -- unroll 1 = if (x<1) then (x:=x+1; assume(¬(x<1))) else skip
  simp only [unroll_while, sp_ite', sp_seq', sp_assign', sp_assume', sp_skip']
  -- Choose the true branch (left disjunct)
  left
  -- Goal: (∃ s, (s "x" = 0 ∧ s "x" < 1) ∧ t = s["x" ↦ s "x" + 1]) ∧ ¬(t "x" < 1)
  constructor
  · -- ∃ s, (s "x" = 0 ∧ s "x" < 1) ∧ t = s["x" ↦ s "x" + 1]
    refine ⟨t["x" ↦ 0], ⟨?_, ?_⟩, ?_⟩
    · simp [State.update]
    · simp [State.update]
    · funext y; unfold State.update
      by_cases hy : y = "x" <;> simp [hy, ht]
  · -- ¬(t "x" < 1)
    omega

-- ============================================
-- Example 8: While loop (2 iterations)
-- ============================================

/-- While loop with 2 iterations: while (x < 2) do x := x + 1
  Precondition: x = 0
  Postcondition: x = 2

  We use vc_while_sound with 2 unrollings. -/
example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 2) (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 2) *] := by
  apply vc_while_sound (k := 2)
  intro t ht
  simp only [unroll_while, sp_ite', sp_seq', sp_assign', sp_assume', sp_skip']
  -- The 2-unrolling creates nested disjunctions. We need the path:
  -- iteration 1 (x<2, x:=x+1) → iteration 2 (x<2, x:=x+1) → exit (¬(x<2))
  -- This is: left branch of outer if, then left branch of inner if
  -- First left: outer if true branch. Second left: inner if true branch (2 iterations).
  left
  left
  -- Goal: (∃ s, ((∃ s₁, (s₁ "x" = 0 ∧ s₁ "x" < 2) ∧ s = s₁["x"↦...]) ∧ s "x" < 2) ∧ t = s["x"↦...]) ∧ ¬(t "x" < 2)
  constructor
  · -- Existential: witness s with x = 1 (after first iteration)
    refine ⟨t["x" ↦ 1], ⟨⟨t["x" ↦ 0], ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp [State.update]             -- 0 = 0
    · simp [State.update]             -- 0 < 2
    · funext y; unfold State.update   -- t["x"↦1] = (t["x"↦0])["x"↦0+1]
      by_cases hy : y = "x" <;> simp [hy]
    · simp [State.update]             -- 1 < 2
    · funext y; unfold State.update   -- t = (t["x"↦1])["x"↦1+1]
      by_cases hy : y = "x" <;> simp [hy, ht]
  · omega                              -- ¬(2 < 2)
