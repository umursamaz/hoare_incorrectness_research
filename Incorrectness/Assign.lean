import Incorrectness.Defs
import PExp
import AExp

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

-- The Assignment Rule from Reverse Hoare Logic Paper
theorem assign_intro_paper {p : PExp} {x : String} {e : AExp} :
    [* fun s => p.eval s *]
    (Stmt.assign x (fun s => e.eval s))
    [* fun t => ∃ oldVal : Nat,
        (p.subst x (AExp.num oldVal)).eval t ∧
        t x = (e.subst x (AExp.num oldVal)).eval t *] := by
  intro t hPost
  cases hPost with
  | intro oldVal hAnd =>
    cases hAnd with
    | intro hP_subst hX_eq =>
      let s := t[x ↦ oldVal]
      exists s
      constructor
      · -- p.eval s
        have h := PExp.subst_lemma p (AExp.num oldVal) x t
        simp [AExp.eval] at h
        rw [h] at hP_subst
        exact hP_subst
      · -- (Stmt.assign x e, s) ⟹ t
        have hEval : (e.subst x (AExp.num oldVal)).eval t = e.eval s := by
          have h := AExp.subst_lemma e (AExp.num oldVal) x t
          simp [AExp.eval] at h
          exact h
        have hTx : e.eval s = t x := by rw [← hEval]; exact hX_eq.symm
        have hEq : s[x ↦ e.eval s] = t := by
          funext y
          simp only [State.update]
          split
          · case isTrue hy =>
            rw [hy, hTx]
          · case isFalse hy =>
            show (t[x ↦ oldVal]) y = t y
            simp [State.update, hy]
        rw [← hEq]
        exact BigStep.assign x (fun s => e.eval s) s


end Incorrectness
