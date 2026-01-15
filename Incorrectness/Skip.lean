import Incorrectness.Defs
open Language
namespace Incorrectness

-- The Skip Rule for Incorrectness Logic
--      [P] skip [P]

theorem skip_intro {P : State → Prop} :
  [* P *] (Stmt.skip) [* P *] :=
  by
  -- Introduce the variables:
  -- s: initial state
  -- t: final state
  intro t hP

  exists t
  apply And.intro

  exact hP
  exact BigStep.skip t

end Incorrectness
