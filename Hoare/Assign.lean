import Hoare.Defs
import PExp
open Language
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

-- PExp-specific assignment rule
theorem assign_intro_pexp {p : Language.PExp} {x : String} {a : Language.AExp} :
    {* fun s => (p.subst x a).eval s *}
    (Language.Stmt.assign x (fun s => a.eval s))
    {* fun s => p.eval s *} := by
  intro s t hPre hStep
  cases hStep
  rw [← Language.PExp.subst_lemma]
  exact hPre
end Hoare
