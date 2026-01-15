import Incorrectness.Defs
open Language
namespace Incorrectness

-- The While Rule (Loop Invariant)
--
--        [P ∧ B] S [P]
-- ---------------------------
-- [P] while B do S [P ∧ ¬B]


theorem while_intro {P : State → Prop}
    {B : State → Prop}
    {S : Stmt} :
  [* P *] (Stmt.whileDo B S) [* fun t => P t ∧ ¬B t *] :=
  by
  -- Introduce variables and hypotheses
  -- t: final state
  -- h_post: hypothesis that P ∧ ¬B holds in state t (postcondition)
  intro t h_post
  cases h_post with
  -- hP: P holds in state t
  -- hNotB: ¬B holds in state t
    | intro hP hNotB =>
    exists t
    apply And.intro
    exact hP
    apply BigStep.while_false
    exact hNotB
