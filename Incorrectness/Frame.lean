import Incorrectness.Defs
open Language
namespace Incorrectness

-- Frame Rule
--
--        ⟨P⟩ c ⟨Q⟩
-- ─────────────────────────────
--     ⟨P ∧ R⟩ c ⟨Q ∧ R⟩


theorem frame
    {P Q R : State → Prop}
    {S : Stmt}
    (hTriple : [* P *] (S) [* Q *])
    (hFrame : ∀ s t, R t → (S, s) ⟹ t → R s)
    : [* fun s => P s ∧ R s *] (S) [* fun t => Q t ∧ R t *] := by
  intro t hPost
  cases hPost with
  | intro hQt hRt =>
    have ⟨s, hPs, hExec⟩ := hTriple t hQt
    have hRs : R s := hFrame s t hRt hExec
    exact ⟨s, ⟨hPs, hRs⟩, hExec⟩

end Incorrectness
