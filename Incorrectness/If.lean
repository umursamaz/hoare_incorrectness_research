import Incorrectness.Defs
open Language
namespace Incorrectness

-- The Conditional Rule (If-Then-Else)
--
--        [P ∧ B] S [Q]    [P ∧ ¬B] T [Q]
-- -------------------------------------------
--        [P] if B then S else T [Q]

theorem if_intro {P Q1 Q2 : State → Prop}
    {B : State → Prop}
    {S1 S2 : Stmt}
  (h1 : [* fun s => P s ∧ B s *] (S1) [* Q1 *])
  (h2 : [* fun s => P s ∧ ¬B s *] (S2) [* Q2 *]) :
  [* P *] (Stmt.ifThenElse B S1 S2) [* fun t => Q1 t ∨ Q2 t *] :=
  by
  -- Introduce variables and hypotheses
  -- t: final state
  -- h_post: hypothesis that the postcondition holds in state t
  intro t h_post

  cases h_post with
  -- CASE 1: The TRUE Branch (S1 executed)
  | inl hQ1 =>
    -- Use hypothesis h1 to find the start state 's'
    -- h1 says: If we are in Q1, we came from 's' where (P s ∧ B s).
    have h1_unfolded := h1 t hQ1
    cases h1_unfolded with
    -- s : The initial state
    -- h_start : (P s ∧ B s) and (S1, s) executes to t
    | intro s h_start =>
      cases h_start with
      -- hPre1  : (P s ∧ B s)
      -- hExec1 : (S1, s) executes to t
      | intro hPre1 hExec1 =>
        exists s
        apply And.intro
        exact hPre1.left

        apply BigStep.if_true B S1 S2 s t
        exact hPre1.right -- Proof that condition B is true
        exact hExec1      -- Proof that S1 executes to t

  -- CASE 2: The FALSE Branch (S2 executed)
  | inr hQ2 =>
    -- Use hypothesis h2 to find the start state 's'
    -- h2 says: If we are in Q2, we came from 's' where (P s ∧ ¬B s).
    have h2_unfolded := h2 t hQ2
    cases h2_unfolded with
    -- s : The initial state
    -- h_start : (P s ∧ ¬B s) and (S2, s) executes to t
    | intro s h_start =>
      cases h_start with
      -- hPre2  : (P s ∧ ¬B s)
      -- hExec2 : (S2, s) executes to t
      | intro hPre2 hExec2 =>
        exists s
        apply And.intro
        exact hPre2.left

        apply BigStep.if_false B S1 S2 s t
        exact hPre2.right -- Proof that condition B is false (¬B)
        exact hExec2      -- Proof that S2 executes to t
end Incorrectness
