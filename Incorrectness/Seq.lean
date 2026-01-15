import Incorrectness.Defs
open Language
namespace Incorrectness

-- The Sequence Rule
-- [P] S [Q]   [Q] T [R]
-- ---------------------
--     [P] S; T [R]
--
-- This is standard composition: [P] S1 [Q] and [Q] S2 [R] implies [P] S1;S2 [R]
--
theorem seq_intro {P Q R : State → Prop} {S1 S2 : Stmt}
  (h1 : [* P *] (S1) [* Q *])
  (h2 : [* Q *] (S2) [* R *]) :
  [* P *] (S1; S2) [* R *] :=
  by
  -- Introduce variables and hypotheses
  -- t: final state
  -- hR: hypothesis that R holds in state t (Postcondition)
  intro t hR

  have h2_unfolded := h2 t hR
  cases h2_unfolded with
  -- s2 : The intermediate state
  -- h_intermediate : Q holds at s2 ∧ (S2, s2) executes to t
  | intro s2 h_intermediate =>
    cases h_intermediate with
  -- hQ     : Q holds at s2
  -- hExec2 : (S2, s2) executes to t
    | intro hQ hExec2 =>
      have h1_unfolded := h1 s2 hQ
      cases h1_unfolded with
      -- s1 : The initial state
      -- h_start : P holds at s1 ∧ (S1, s1) executes to s2
      | intro s1 h_start =>
        cases h_start with
      -- hP     : P holds at s1
      -- hExec1 : (S1, s1) executes to s2
        | intro hP hExec1 =>
        exists s1

        apply And.intro
        exact hP
        exact BigStep.seq S1 S2 s1 s2 t hExec1 hExec2

end Incorrectness
