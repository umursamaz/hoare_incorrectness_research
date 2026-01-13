import Hoare.Defs
namespace Hoare

-- The Assignment Rule
-- {P[x ↦ a]} x := a {P}

theorem assign_intro {P : State → Prop}
    {x : String}
    {a : State → Nat} :
  {* fun s => P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  by
  -- Introduction
  -- s: initial state
  -- t: final state
  -- hP: hypothesis (Precondition holds for the updated state)
  -- hStep: hypothesis (Execution step of assignment)
  intro s t hP hStep
  cases hStep
  exact hP
end Hoare
