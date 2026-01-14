import Hoare.Defs
open Language
namespace Hoare
-- The While Rule (Loop Invariant)
--
--        {P ∧ B} S {P}
-- ---------------------------
-- {P} while B do S {P ∧ ¬B}
--
-- Logic:
-- P is the loop invariant - it holds before and after each iteration.
-- When the loop terminates, B must be false, so we get P ∧ ¬B.
theorem while_intro (P : State → Prop)
    {B : State → Prop}
    {S : Stmt}
    (h : {* fun s => P s ∧ B s *} (S) {* P *}) :
  {* P *} (Stmt.whileDo B S) {* fun s => P s ∧ ¬ B s *} :=
  by
  -- Introduce variables and hypotheses
  -- s: initial state
  -- t: final state
  -- hP: hypothesis that P holds in state s (loop invariant initially true)
  -- hStep: hypothesis that the while loop executed from s to t
  intro s t hP hStep
  generalize hEq : (Stmt.whileDo B S, s) = pair
  rw [hEq] at hStep
  induction hStep generalizing s with
  | skip si =>                                cases hEq
  | assign x a si =>                          cases hEq
  | seq S T si sm sf hS hT ihS ihT =>         cases hEq
  | if_true Bx Sx Tx si sf hCond hBody ih =>  cases hEq
  | if_false Bx Sx Tx si sf hCond hBody ih => cases hEq
  | while_true Bx Sx si sm sf hCond hBody hRest ihBody ihRest =>
    cases hEq
    apply ihRest
    · apply h
      · exact And.intro hP hCond
      · exact hBody
    rfl
  | while_false Bx Sx si hCond =>
    cases hEq
    exact And.intro hP hCond

end Hoare
