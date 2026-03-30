import Incorrectness.SP

open Language
open Incorrectness

/-!
# VC Generation Tactics for Incorrectness Logic

This file provides Lean tactics that automate the repetitive parts
of VC-based IL proofs:

1. `state_ext` — proves state equalities by pointwise case analysis
2. `il_vc` — sets up the VC proof structure (apply vc_sound + intro + simp)
3. `il_vc_while` — sets up VC for while loops with bounded unrolling

These tactics eliminate the manual `funext y; unfold State.update;
by_cases hy : y = "x" <;> simp [hy, ...]` pattern that appears
in every assignment-related VC proof.
-/

-- ============================================
-- Core Tactic: state_ext
-- ============================================

/-- Proves goals of the form `t = s["x" ↦ v]` or `s["x" ↦ v] = t`
    by extensionality + unfolding State.update + simp.
    Covers the most common VC subgoal pattern. -/
macro "state_ext" : tactic =>
  `(tactic| (funext _v; simp only [State.update]; split <;> simp_all <;> try omega))

-- ============================================
-- VC Setup Tactics
-- ============================================

/-- Sets up a VC proof for a loop-free IL triple.
    Applies vc_sound, introduces the final state and postcondition hypothesis,
    then unfolds sp definitions. -/
macro "il_vc" : tactic =>
  `(tactic| (apply vc_sound; intro _ _; simp only [sp_skip', sp_assign', sp_seq',
             sp_ite', sp_assume', sp_assert']))

/-- Sets up a VC proof for a while loop IL triple with k unrollings.
    Applies vc_while_sound, introduces the final state and postcondition,
    then unfolds sp + unroll_while definitions. -/
syntax "il_vc_while" num : tactic
macro_rules
  | `(tactic| il_vc_while $k) =>
    `(tactic| (apply vc_while_sound (k := $k); intro _ _;
               simp only [unroll_while, sp_skip', sp_assign', sp_seq',
                           sp_ite', sp_assume', sp_assert']))
