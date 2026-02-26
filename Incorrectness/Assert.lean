import Incorrectness.Defs
open Language
namespace Incorrectness

theorem assert_intro {P : State → Prop} {B : State → Prop} :
    [* fun s => P s ∧ B s *] (Stmt.assert B) [* fun s => P s ∧ B s *] := by
  intro t hPost
  obtain ⟨hPt, hBt⟩ := hPost
  exists t
  constructor
  · exact ⟨hPt, hBt⟩
  · exact BigStep.assert B t hBt

end Incorrectness
