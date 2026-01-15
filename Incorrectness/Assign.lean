import Incorrectness.Defs
open Language
namespace Incorrectness

-- The Assignment Rule
-- Q = { t | ∃ s, P s ∧ t = s[x ↦ a s] }
--
theorem assign_intro {P : State → Prop}
    {x : String}
    {a : State → Nat} :
  [* P *] (Stmt.assign x a) [* fun t => ∃ s, P s ∧ t = (s[x ↦ a s]) *] :=
  by
  -- Introduction
  -- t: final state
  -- h_post: hypothesis (Postcondition holds for the final state)
  intro t h_post

  cases h_post with
      -- s_prev : The previous state
      -- h_and  : hypothesis (P holds for s_prev ∧ t = s_prev[x ↦ a s_prev])
    | intro s_prev h_and =>
      cases h_and with
        -- hP     : P holds for s_prev
        -- hEq    : t is indeed s_prev updated with x assigned to (a s_prev)
      | intro hP hEq =>
        exists s_prev

        apply And.intro
        exact hP

        rw [hEq]
        exact BigStep.assign x a s_prev

end Incorrectness
