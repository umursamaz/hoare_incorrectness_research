import Hoare.Defs
namespace Hoare

-- The Sequence Rule
-- {P} S {Q}   {Q} T {R}
-- ---------------------
--     {P} S; T {R}

theorem seq_intro {P Q R : State → Prop}
    {S T : Stmt}
    (hS : {* P *} (S) {* Q *})
    (hT : {* Q *} (T) {* R *}) :
  {* P *} (S; T) {* R *} :=
  by
  -- Introduce variables and hypotheses
  -- s: initial state
  -- u: final state (after both S and T run)
  -- hP: hypothesis that P holds in state s (Precondition)
  -- hStep: hypothesis that the sequence (S; T) executed from s to u
  intro s u hP hStep

  cases hStep with
  | seq _ _ _ t _ hS_exec hT_exec =>
    -- It is the same thing with "| seq S T s t u hS_exec hT_exec =>"

    have hQ := hS s t hP hS_exec
    have hR := hT t u hQ hT_exec
    exact hR

end Hoare
