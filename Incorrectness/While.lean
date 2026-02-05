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


-- Helper lemma: From P n state, we can reach back to P 0 state
-- building the while loop execution along the way
theorem while_iterations_aux
    {P : Nat → State → Prop}
    {B : State → Prop}
    {S : Stmt}
    (hBody : ∀ i, [* fun s => P i s ∧ B s *] (S) [* fun s => P (i + 1) s *])
    : ∀ n sn t,
        P n sn →
        (Stmt.whileDo B S, sn) ⟹ t →
        ∃ s0, P 0 s0 ∧ (Stmt.whileDo B S, s0) ⟹ t := by
  intro n
  induction n with
  | zero =>
    intro s0 t hP0 hExec
    exact ⟨s0, hP0, hExec⟩
  | succ n ih =>
    intro sn1 t hPsucc hExec
    have hBodyN := hBody n sn1 hPsucc
    cases hBodyN with
    | intro sn hAnd =>
      cases hAnd with
      | intro hPnB hStepS =>
        cases hPnB with
        | intro hPn hBsn =>
          have hWholeExec : (Stmt.whileDo B S, sn) ⟹ t :=
            BigStep.while_true B S sn sn1 t hBsn hStepS hExec
          exact ih sn t hPn hWholeExec

theorem while_intro_paper
    {P : Nat → State → Prop}
    {B : State → Prop}
    {S : Stmt}
    (hBody : ∀ i, [* fun s => P i s ∧ B s *] (S) [* fun s => P (i + 1) s *])
    :
    [* P 0 *] (Stmt.whileDo B S) [* fun t => ¬B t ∧ ∃ i, P i t *] := by
  intro t hPost
  cases hPost with
  | intro hNotB hExists =>
    cases hExists with
    | intro i hPi =>
      have hExecFromT : (Stmt.whileDo B S, t) ⟹ t :=
        BigStep.while_false B S t hNotB
      exact while_iterations_aux hBody i t t hPi hExecFromT
end Incorrectness
