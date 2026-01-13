import Hoare.Defs
namespace Hoare

-- The Conditional Rule (If-Then-Else)
--
--        {P ∧ B} S {Q}    {P ∧ ¬B} T {Q}
-- -------------------------------------------
--        {P} if B then S else T {Q}
--
-- Logic:
-- 1. If condition B is true, we execute S. We must prove S takes us to Q.
-- 2. If condition B is false, we execute T. We must prove T takes us to Q.

theorem if_intro {B P Q: State → Prop}
    {S T : Stmt}
  (hS : {* fun s => P s ∧ B s *} (S) {* Q *})
  (hT : {* fun s => P s ∧ ¬ B s *} (T) {* Q *}) :
  {* P *} (Stmt.ifThenElse B S T) {* Q *} :=
  by
  -- 1. Intro Step:
  -- s: initial state, t: final state
  -- hP: Precondition P holds in s
  -- hStep: The 'if' statement executed from s to t
  intro s t hP hStep
  cases hStep with

  | if_true _ _ _ _ _ hCond hBody =>
    -- We need to prove Q t.
    -- Use the hypothesis hS (behavior of S).
    -- It needs: (P s ∧ B s) and the execution step.
    have hPre : P s ∧ B s := And.intro hP hCond
    have hResult := hS s t hPre hBody
    exact hResult

  | if_false _ _ _ _ _ hCond hBody =>
    -- We need to prove Q t.
    -- Use the hypothesis hT (behavior of T).
    -- It needs: (P s ∧ ¬B s) and the execution step.
    have hPre : P s ∧ ¬ B s := And.intro hP hCond
    have hResult := hT s t hPre hBody
    exact hResult

end Hoare
