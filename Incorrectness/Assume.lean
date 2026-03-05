import Incorrectness.Defs
open Language
namespace Incorrectness

-- Assume Rule (from O'Hearn paper, Figure 2)
-- [p] assume B [ok: p ∧ B]
--
-- In the ok-only model (without er exit conditions),
-- assume B succeeds only when B holds, leaving state unchanged.
-- This matches the paper's: [p] assume B [ok: p ∧ B] [er: false]

theorem assume_intro {P : State → Prop} {B : State → Prop} :
    [* fun s => P s ∧ B s *] (Stmt.assume B) [* fun s => P s ∧ B s *] := by
  intro t ⟨hPt, hBt⟩
  exact ⟨t, ⟨hPt, hBt⟩, BigStep.assume B t hBt⟩

end Incorrectness
