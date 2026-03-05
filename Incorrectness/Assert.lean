import Incorrectness.Defs
open Language
namespace Incorrectness

-- Assert Rule: OK path (from O'Hearn paper p.11)
-- [p ∧ B] assert(B) [ok: p ∧ B] [er: false]
--
-- When the condition holds, assert succeeds and state is unchanged.
theorem assert_ok_intro {P : State → Prop} {B : State → Prop} :
    [* fun s => P s ∧ B s *] (Stmt.assert B) [* fun s => P s ∧ B s *] := by
  intro t ⟨hPt, hBt⟩
  exact ⟨t, ⟨hPt, hBt⟩, BigStep.assert_ok B t hBt⟩

-- Assert Rule: Error path (from O'Hearn paper p.11)
-- [p ∧ ¬B] assert(B) [ok: false] [er: p ∧ ¬B]
--
-- When the condition fails, assert raises an error. State is unchanged.
-- In our model (without separate ok/er triples), this captures
-- the execution where assert's condition is false.
theorem assert_er_intro {P : State → Prop} {B : State → Prop} :
    [* fun s => P s ∧ ¬B s *] (Stmt.assert B) [* fun s => P s ∧ ¬B s *] := by
  intro t ⟨hPt, hNotBt⟩
  exact ⟨t, ⟨hPt, hNotBt⟩, BigStep.assert_er B t hNotBt⟩

-- Combined Assert Rule (from O'Hearn paper p.11)
-- [p] assert(B) [ok: p ∧ B] [er: p ∧ ¬B]
--
-- General form: given any precondition P, assert splits into
-- the ok path (where B holds) and the error path (where B fails).
-- Since we don't have separate ok/er triples, we express this as:
-- [p] assert(B) [p]  (state unchanged in both cases)
theorem assert_intro {P : State → Prop} {B : State → Prop} :
    [* P *] (Stmt.assert B) [* P *] := by
  intro t hPt
  by_cases hB : B t
  · exact ⟨t, hPt, BigStep.assert_ok B t hB⟩
  · exact ⟨t, hPt, BigStep.assert_er B t hB⟩

end Incorrectness
