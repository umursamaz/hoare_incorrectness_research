import Incorrectness.Defs
open Language
namespace Incorrectness

-- Consequence Rule
--
--  P' ⇒ P    ⟨P'⟩ c ⟨Q'⟩    Q ⇒ Q'
-- ─────────────────────────────────
--         ⟨P⟩ c ⟨Q⟩

theorem consequence
    {P P' Q Q' : State → Prop}
    {S : Stmt}
    (hP : ∀ s, P' s → P s)
    (hTriple : [* P' *] (S) [* Q' *])
    (hQ : ∀ s, Q s → Q' s)
    : [* P *] (S) [* Q *] := by
  intro t hQt
  -- hQt : Q t
  -- We need: ∃ s, P s ∧ (S, s) ⟹ t
  have hQ't : Q' t := hQ t hQt
  have ⟨s, hP's, hExec⟩ := hTriple t hQ't
  exact ⟨s, hP s hP's, hExec⟩

end Incorrectness
