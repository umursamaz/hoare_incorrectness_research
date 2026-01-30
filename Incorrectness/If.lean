import Incorrectness.Defs
open Language
namespace Incorrectness

-- The Conditional Rule (If-Then-Else)
-- THEN:                            ELSE:
--      ⟨P ∧ b⟩ c₀ ⟨Q⟩                       ⟨P ∧ ¬b⟩ c₁ ⟨Q⟩
--   ──────────────────────             ──────────────────────
-- ⟨P⟩ if b then c₀ else c₁ ⟨Q⟩       ⟨P⟩ if b then c₀ else c₁ ⟨Q⟩
--


theorem if_then {P Q : State → Prop}
    {B : State → Prop}
    {S1 S2 : Stmt}
    (h : [* fun s => P s ∧ B s *] (S1) [* Q *]) :
    [* P *] (Stmt.ifThenElse B S1 S2) [* Q *] := by
  intro t hQ
  obtain ⟨s, hS⟩ := h t hQ
  exact ⟨s, hS.1.1, BigStep.if_true B S1 S2 s t hS.1.2 hS.2⟩

theorem if_else {P Q : State → Prop}
    {B : State → Prop}
    {S1 S2 : Stmt}
    (h : [* fun s => P s ∧ ¬B s *] (S2) [* Q *]) :
    [* P *] (Stmt.ifThenElse B S1 S2) [* Q *] := by
  intro t hQ
  obtain ⟨s,hS⟩ := h t hQ
  exact ⟨s, hS.1.1, BigStep.if_false B S1 S2 s t hS.1.2 hS.2⟩


-- end Incorrectness
