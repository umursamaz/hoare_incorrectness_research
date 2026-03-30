import Incorrectness.VCGen

open Language
open Incorrectness

/-!
# VC Examples with Tactic Automation

These examples demonstrate the same IL triples as SPExamples.lean,
but using the VCGen tactics for shorter, more readable proofs.

**Comparison:** Each example shows how `il_vc`, `il_vc_while`, and
`state_ext` reduce the proof burden compared to manual proofs.
-/

-- ============================================
-- Example 1: Skip (trivial — same as manual)
-- ============================================

example : [* (fun s => s "x" = 5) *]
          (Stmt.skip)
          [* (fun s => s "x" = 5) *] := by
  il_vc
  assumption

-- ============================================
-- Example 2: Assume
-- ============================================

example : [* (fun _ => True) *]
          (Stmt.assume (fun s => s "x" > 0))
          [* (fun s => s "x" > 0) *] := by
  il_vc
  exact ⟨trivial, ‹_›⟩

-- ============================================
-- Example 3: Assignment (q = sp, identity VC)
-- ============================================

example : [* (fun s => s "x" = 0) *]
          (Stmt.assign "x" (fun s => s "x" + 1))
          [* (fun t => ∃ s, s "x" = 0 ∧ t = s["x" ↦ s "x" + 1]) *] := by
  il_vc
  assumption

-- ============================================
-- Example 4: Assignment with simplified postcondition
-- Manual proof was 8 lines. Tactic proof: 5 lines.
-- ============================================

example : [* (fun s => s "x" = 0) *]
          (Stmt.assign "x" (fun s => s "x" + 1))
          [* (fun t => t "x" = 1) *] := by
  il_vc
  -- Goal: ∃ s, s "x" = 0 ∧ t = s["x" ↦ s "x" + 1]
  rename_i t ht
  refine ⟨t["x" ↦ 0], ?_, ?_⟩
  · simp [State.update]
  · state_ext

-- ============================================
-- Example 5: Sequence (x := 1; y := x + 1)
-- Manual proof was 10 lines. Tactic proof: 8 lines.
-- ============================================

example : [* (fun _ => True) *]
          (Stmt.seq
            (Stmt.assign "x" (fun _ => 1))
            (Stmt.assign "y" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 1 ∧ t "y" = 2) *] := by
  il_vc
  rename_i t ht
  obtain ⟨htx, hty⟩ := ht
  refine ⟨t["y" ↦ 0], ⟨t["y" ↦ 0]["x" ↦ 0], trivial, ?_⟩, ?_⟩
  · state_ext
  · state_ext

-- ============================================
-- Example 6: If-then-else
-- ============================================

example : [* (fun s => s "x" > 0) *]
          (Stmt.ifThenElse
            (fun s => s "x" > 0)
            (Stmt.assign "y" (fun _ => 1))
            (Stmt.assign "y" (fun _ => 0)))
          [* (fun t => t "y" = 1 ∧ t "x" > 0) *] := by
  il_vc
  rename_i t ht
  obtain ⟨hty, htx⟩ := ht
  left
  refine ⟨t["y" ↦ 0], ⟨?_, ?_⟩, ?_⟩
  · simp [State.update]; exact htx
  · simp [State.update]; exact htx
  · state_ext

-- ============================================
-- Example 7: While loop (1 iteration)
-- ============================================

example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 1) (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 1) *] := by
  il_vc_while 1
  rename_i t ht
  left
  constructor
  · refine ⟨t["x" ↦ 0], ⟨?_, ?_⟩, ?_⟩
    · simp [State.update]
    · simp [State.update]
    · state_ext
  · omega

-- ============================================
-- Example 8: While loop (2 iterations)
-- ============================================

example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 2) (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 2) *] := by
  il_vc_while 2
  rename_i t ht
  left; left
  constructor
  · refine ⟨t["x" ↦ 1], ⟨⟨t["x" ↦ 0], ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp [State.update]
    · simp [State.update]
    · state_ext
    · simp [State.update]
    · state_ext
  · omega

-- ============================================
-- Example 9: While loop (3 iterations)
-- Demonstrates scalability of the approach.
-- ============================================

example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 3) (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 3) *] := by
  il_vc_while 3
  rename_i t ht
  left; left; left
  constructor
  · refine ⟨t["x" ↦ 2], ⟨⟨t["x" ↦ 1], ⟨⟨t["x" ↦ 0], ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp [State.update]
    · simp [State.update]
    · state_ext
    · simp [State.update]
    · state_ext
    · simp [State.update]
    · state_ext
  · omega

-- ============================================
-- Example 10: inc() from paper (assert + assign)
-- Same as Examples.lean inc_example, but via VC approach
-- ============================================

example : [* (fun s => s "x" ≥ 0) *]
          (Stmt.seq
            (Stmt.assert (fun s => s "x" ≥ 0))
            (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" > 0) *] := by
  apply vc_sound
  intro t ht
  simp only [sp_seq', sp_assert', sp_assign']
  exact ⟨t["x" ↦ t "x" - 1], by simp [State.update], by state_ext⟩
