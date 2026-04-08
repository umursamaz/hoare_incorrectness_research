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

-- ============================================
-- Example 11: client() from O'Hearn Figure 9
-- Two inc()s in sequence: [x ≥ 0] inc(); inc() [x > 1]
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
  il_vc
  rename_i t ht
  refine ⟨t["x" ↦ t "x" - 1], ⟨t["x" ↦ t "x" - 2], Nat.zero_le _, ?_⟩, ?_⟩
  · state_ext
  · state_ext

-- ============================================
-- Example 12: test() from O'Hearn Figure 9
-- [true] x:=0; inc(); inc(); assert(x≥2) [x=2 ∧ x≥2]
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
  apply vc_sound
  intro t ⟨htx, _⟩
  simp only [sp_seq', sp_assert', sp_assign']
  refine ⟨t["x" ↦ 1], ⟨t["x" ↦ 0], ⟨t, trivial, rfl⟩, ?_⟩, ?_⟩
  · state_ext
  · state_ext

-- ============================================
-- Example 13: Assert error path
-- [true] x:=0; assert(x>0) [x=0]
-- Assert FAILS (0 is not > 0), but the error state is reachable.
-- ============================================

example : [* (fun _ => True) *]
          (Stmt.seq
            (Stmt.assign "x" (fun _ => 0))
            (Stmt.assert (fun s => s "x" > 0)))
          [* (fun t => t "x" = 0) *] := by
  il_vc
  rename_i t ht
  exact ⟨t, trivial, by state_ext⟩

-- ============================================
-- Example 14: If-else (under-approximation from else branch)
-- [x=3] if x>5 then y:=10 else y:=20 [y=20 ∧ x=3]
-- Only the else branch is needed (under-approximation).
-- ============================================

example : [* (fun s => s "x" = 3) *]
          (Stmt.ifThenElse
            (fun s => s "x" > 5)
            (Stmt.assign "y" (fun _ => 10))
            (Stmt.assign "y" (fun _ => 20)))
          [* (fun t => t "y" = 20 ∧ t "x" = 3) *] := by
  il_vc
  rename_i t ht
  obtain ⟨hty, htx⟩ := ht
  right
  refine ⟨t["y" ↦ 0], ⟨?_, ?_⟩, ?_⟩
  · simp [State.update]; omega
  · simp [State.update]; omega
  · state_ext

-- ============================================
-- Example 15: Assume in sequence
-- [true] assume(x>0); x:=x+1 [x>1]
-- Assume filters precondition, then assignment.
-- ============================================

example : [* (fun _ => True) *]
          (Stmt.seq
            (Stmt.assume (fun s => s "x" > 0))
            (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" > 1) *] := by
  il_vc
  rename_i t ht
  refine ⟨t["x" ↦ t "x" - 1], ⟨trivial, ?_⟩, ?_⟩
  · simp [State.update]; omega
  · state_ext

-- ============================================
-- Invariant-Based While Loop Examples
-- ============================================
-- These examples use vc_while_inv_sound with indexed invariants.
-- Key advantage: proof size is CONSTANT regardless of iteration count.

-- ============================================
-- Example 16: While loop (1 iteration, invariant-based)
-- Compare with Example 7 (bounded unrolling).
-- Same triple, but using invariant Inv(i)(s) = (s "x" = i ∧ i ≤ 1).
-- ============================================

example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 1) (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 1) *] := by
  apply vc_while_inv_sound
    (Inv := fun i s => s "x" = i ∧ i ≤ 1)
  -- VC 1 (hPre): Inv 0 s → P s
  · intro s ⟨hx, _⟩; exact hx
  -- VC 2 (hBody): ∀ i, Inv (i+1) t → sp S (Inv i ∧ B) t
  · intro i t ⟨htx, hle⟩
    simp only [sp_assign']
    have hi : i = 0 := by omega
    subst hi
    refine ⟨t["x" ↦ 0], ⟨?_, ?_⟩, ?_⟩
    · simp [State.update]
    · simp [State.update]
    · state_ext
  -- VC 3 (hPost): Q t → ¬B t ∧ ∃ i, Inv i t
  · intro t ht
    exact ⟨by omega, 1, ht, by omega⟩

-- ============================================
-- Example 17: While loop (3 iterations, invariant-based)
-- Compare with Example 9 (bounded unrolling, 15+ lines).
-- Same proof size as Example 16 — that's the point!
-- Inv(i)(s) = (s "x" = i ∧ i ≤ 3).
-- ============================================

example : [* (fun s => s "x" = 0) *]
          (Stmt.whileDo (fun s => s "x" < 3) (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = 3) *] := by
  apply vc_while_inv_sound
    (Inv := fun i s => s "x" = i ∧ i ≤ 3)
  -- VC 1 (hPre): Inv 0 s → P s
  · intro s ⟨hx, _⟩; exact hx
  -- VC 2 (hBody): ∀ i, Inv (i+1) t → sp S (Inv i ∧ B) t
  · intro i t ⟨htx, hle⟩
    simp only [sp_assign']
    refine ⟨t["x" ↦ i], ⟨?_, ?_⟩, ?_⟩
    · simp [State.update]; omega
    · simp [State.update]; omega
    · state_ext
  -- VC 3 (hPost): Q t → ¬B t ∧ ∃ i, Inv i t
  · intro t ht
    exact ⟨by omega, 3, ht, by omega⟩

-- ============================================
-- Example 18: While loop (parametric n iterations)
-- THIS IS IMPOSSIBLE WITH BOUNDED UNROLLING.
-- [x=0 ∧ n>0] while x<n do x:=x+1 [x=n ∧ n>0]
-- Inv(i)(s) = (s "x" = i ∧ i ≤ s "n" ∧ s "n" > 0).
-- ============================================

example : [* (fun s => s "x" = 0 ∧ s "n" > 0) *]
          (Stmt.whileDo (fun s => s "x" < s "n") (Stmt.assign "x" (fun s => s "x" + 1)))
          [* (fun t => t "x" = t "n" ∧ t "n" > 0) *] := by
  apply vc_while_inv_sound
    (Inv := fun i s => s "x" = i ∧ i ≤ s "n" ∧ s "n" > 0)
  -- VC 1 (hPre): Inv 0 s → P s
  · intro s ⟨hx, _, hn⟩; exact ⟨hx, hn⟩
  -- VC 2 (hBody): ∀ i, Inv (i+1) t → sp S (Inv i ∧ B) t
  · intro i t ⟨htx, hle, hn⟩
    simp only [sp_assign']
    refine ⟨t["x" ↦ i], ⟨?_, ?_⟩, ?_⟩
    · simp [State.update]; omega
    · simp [State.update]; omega
    · state_ext
  -- VC 3 (hPost): Q t → ¬B t ∧ ∃ i, Inv i t
  · intro t ⟨hxn, hn⟩
    exact ⟨by omega, t "n", hxn, by omega, hn⟩
