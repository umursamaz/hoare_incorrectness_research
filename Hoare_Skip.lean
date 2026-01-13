import Hoare_Defs

-- The Skip Rule
-- {P} skip {P}

theorem skip_intro {P : State → Prop} :
  {* P *} (Stmt.skip) {* P *} :=
  by
  -- Introduce the variables:
  -- s: initial state
  -- t: final state
  -- hP: hypothesis that P holds in state s
  -- hStep: hypothesis that (skip, s) evaluates to t
  intro s t hP hStep
  cases hStep
  exact hP
