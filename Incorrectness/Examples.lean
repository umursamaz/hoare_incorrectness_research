import Incorrectness.Defs
import Incorrectness.Assign
import Incorrectness.Seq
import Incorrectness.Skip
import Incorrectness.Cons
import Incorrectness.Frame
import Incorrectness.While
import Incorrectness.If
import Incorrectness.Assert
import PExp
import AExp

open Language Incorrectness
namespace Incorrectness.Examples



-- ============================================================
-- Figure 9, Example 1: inc()
-- void inc() { assert(x >= 0); x = x + 1; }
--
-- Note: The triple [x >= 0] inc() [x >= 0] is NOT valid as an
-- incorrectness triple because t "x" = 0 has no predecessor
-- under x := x + 1 (no natural number n satisfies n + 1 = 0).
-- Instead, we prove the valid triple: [x >= 0] inc() [x > 0]
-- This corresponds to "presumes1: [x>=0], achieves1: [ok: x>0]"
-- from Figure 9 of the paper.
-- ============================================================

-- Step 1: [x >= 0] assert(x >= 0) [x >= 0]
theorem inc_assert_step :
    [* fun s => s "x" ≥ 0 *]
    (Stmt.assert (fun s => s "x" ≥ 0))
    [* fun s => s "x" ≥ 0 *] := by
  apply consequence
    (P' := fun s => s "x" ≥ 0 ∧ s "x" ≥ 0)
    (Q' := fun s => s "x" ≥ 0 ∧ s "x" ≥ 0)
  · intro s ⟨h, _⟩; exact h
  · exact assert_intro
  · intro s h; exact ⟨h, h⟩

-- Step 2: [x >= 0] x := x + 1 [x > 0]
theorem inc_assign_step :
    [* fun s => s "x" ≥ 0 *]
    (Stmt.assign "x" (fun s => s "x" + 1))
    [* fun t => t "x" > 0 *] := by
  intro t hPost
  let s : State := t["x" ↦ t "x" - 1]
  exists s
  constructor
  · -- s "x" >= 0 (always true for Nat)
    exact Nat.zero_le _
  · -- (x := x + 1, s) ⟹ t
    have hEq : s["x" ↦ s "x" + 1] = t := by
      funext y
      simp only [State.update]
      split
      · case isTrue hy =>
        subst hy
        have : s "x" = t "x" - 1 := by
          simp [s, State.update]
        rw [this]
        omega
      · case isFalse hy =>
        show (t["x" ↦ t "x" - 1]) y = t y
        simp [State.update, hy]
    rw [← hEq]
    exact BigStep.assign "x" (fun s => s "x" + 1) s

-- Combining: [x >= 0] assert(x >= 0); x := x + 1 [x > 0]
theorem inc_example :
    [* fun s => s "x" ≥ 0 *]
    (Stmt.seq
      (Stmt.assert (fun s => s "x" ≥ 0))
      (Stmt.assign "x" (fun s => s "x" + 1)))
    [* fun t => t "x" > 0 *] := by
  exact seq_intro inc_assert_step inc_assign_step


-- ============================================================
-- Figure 9, Example 2: client()
-- void client() { inc(); inc(); }
-- Triple: [x >= 0] inc(); inc() [x > 0]
--
-- Note: Paper shows "wrong achieves1: [x>0]" for presumes1: [x>=0]
-- meaning [x>=0] client() [x>0] should NOT be valid.
-- The issue is that after two increments, x >= 2, not just x > 0.
-- But as an under-approximation [x>=0] client() [x>0] IS valid
-- because every t with x>0 can be reached.
-- Actually paper marks it as "wrong" because it's not precise enough.
-- We prove the valid triple: [x >= 0] client() [x > 0]
-- ============================================================

-- Helper: [x > 0] inc() [x > 0]
-- Since x > 0 implies x >= 0, we can use inc_example with consequence
theorem inc_from_positive :
    [* fun s => s "x" > 0 *]
    (Stmt.seq
      (Stmt.assert (fun s => s "x" ≥ 0))
      (Stmt.assign "x" (fun s => s "x" + 1)))
    [* fun t => t "x" > 1 *] := by
  intro t hPost
  let s : State := t["x" ↦ t "x" - 1]
  exists s
  constructor
  · show (t["x" ↦ t "x" - 1]) "x" > 0
    simp [State.update]
    omega
  · apply BigStep.seq
    · apply BigStep.assert_ok
      exact Nat.zero_le _
    · have hEq : s["x" ↦ s "x" + 1] = t := by
        funext y
        simp only [State.update]
        split
        · case isTrue hy =>
          subst hy
          have : s "x" = t "x" - 1 := by simp [s, State.update]
          rw [this]
          omega
        · case isFalse hy =>
          show (t["x" ↦ t "x" - 1]) y = t y
          simp [State.update, hy]
      rw [← hEq]
      exact BigStep.assign "x" (fun s => s "x" + 1) s

theorem client_example :
    [* fun s => s "x" ≥ 0 *]
    (Stmt.seq
      (Stmt.seq
        (Stmt.assert (fun s => s "x" ≥ 0))
        (Stmt.assign "x" (fun s => s "x" + 1)))
      (Stmt.seq
        (Stmt.assert (fun s => s "x" ≥ 0))
        (Stmt.assign "x" (fun s => s "x" + 1))))
    [* fun t => t "x" > 1 *] := by
  exact seq_intro inc_example inc_from_positive


-- ============================================================
-- Figure 9, Example 3: test()
-- void test() { x = 0; client(); assert(x >= 2); }
--
-- Paper shows: wrong achieves1: [er: x==1], achieves2: [er: false]
-- This means the error path is unreachable - assert never fails.
-- We prove the ok path: [true] test() [x = 2 ∧ x >= 2]
-- ============================================================

theorem test_example :
    [* fun _ => True *]
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
    [* fun t => t "x" = 2 ∧ t "x" ≥ 2 *] := by
  intro t ⟨hX2, hXge⟩
  let s_init : State := t
  let s0 : State := t["x" ↦ 0]
  let s1 : State := t["x" ↦ 1]
  exists s_init
  constructor
  · trivial
  · apply BigStep.seq _ _ s_init t t
    · -- (x:=0; inc(); inc(), s_init) ⟹ t
      apply BigStep.seq _ _ s_init s0 t
      · -- (x := 0, s_init) ⟹ s0
        show (Stmt.assign "x" (fun _ => 0), s_init) ⟹ s0
        exact BigStep.assign "x" (fun _ => 0) s_init
      · -- (inc(); inc(), s0) ⟹ t
        apply BigStep.seq _ _ s0 s1 t
        · -- (assert(x>=0); x:=x+1, s0) ⟹ s1
          apply BigStep.seq
          · -- assert at s0
            exact BigStep.assert_ok (fun s => s "x" ≥ 0) s0 (Nat.zero_le _)
          · show (Stmt.assign "x" (fun s => s "x" + 1), s0) ⟹ s1
            have h01 : s0["x" ↦ s0 "x" + 1] = s1 := by
              funext y; simp only [State.update, s0, s1]
              split <;> simp
            rw [← h01]
            exact BigStep.assign "x" (fun s => s "x" + 1) s0
        · -- (assert(x>=0); x:=x+1, s1) ⟹ t
          apply BigStep.seq
          · -- assert at s1
            exact BigStep.assert_ok (fun s => s "x" ≥ 0) s1 (Nat.zero_le _)
          · show (Stmt.assign "x" (fun s => s "x" + 1), s1) ⟹ t
            have h12 : s1["x" ↦ s1 "x" + 1] = t := by
              funext y; simp only [State.update, s1]
              split
              · case isTrue hy => simp [hy, hX2]
              · case isFalse hy => rfl
            rw [← h12]
            exact BigStep.assign "x" (fun s => s "x" + 1) s1
    · -- (assert(x>=2), t) ⟹ t
      exact BigStep.assert_ok (fun s => s "x" ≥ 2) t hXge


end Incorrectness.Examples
