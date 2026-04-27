import Incorrectness.SP
import Incorrectness.While

open Language
open Incorrectness
open Lean Elab Tactic

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
elab "state_ext" : tactic => do
  evalTactic (← `(tactic| funext _v))
  evalTactic (← `(tactic| simp only [State.update]))
  evalTactic (← `(tactic| split <;> simp_all <;> try omega))

-- ============================================
-- VC Setup Tactics
-- ============================================

/-- Sets up a VC proof for a loop-free IL triple.
    Applies vc_sound, introduces the final state and postcondition hypothesis,
    then unfolds sp definitions. -/
elab "il_vc" : tactic => do
  evalTactic (← `(tactic| apply vc_sound))
  evalTactic (← `(tactic| intro _ _))
  evalTactic (← `(tactic| simp only [sp_skip', sp_assign', sp_seq',
                           sp_ite', sp_assume', sp_assert']))

/-- Sets up a VC proof for a while loop IL triple with k unrollings.
    Applies vc_while_sound, introduces the final state and postcondition,
    then unfolds sp + unroll_while definitions. -/
syntax "il_vc_while" num : tactic
elab_rules : tactic
  | `(tactic| il_vc_while $k) => do
    evalTactic (← `(tactic| apply vc_while_sound (k := $k)))
    evalTactic (← `(tactic| intro _ _))
    evalTactic (← `(tactic| simp only [unroll_while, sp_skip', sp_assign', sp_seq',
                             sp_ite', sp_assume', sp_assert']))

-- ============================================
-- Invariant-Based While VC Tactics
-- ============================================

/-- Sets up the body VC for invariant-based while loop proofs.
    After `apply vc_while_inv_sound`, each body goal has the form
    `∀ i t, Inv (i+1) t → sp S (Inv i ∧ B) t`.
    This tactic introduces variables and unfolds sp. -/
elab "il_vc_inv_body" : tactic => do
  evalTactic (← `(tactic| intro _ _))
  evalTactic (← `(tactic| simp only [sp_skip', sp_assign', sp_seq',
                           sp_ite', sp_assume', sp_assert']))

-- ============================================
-- Automated IL Prover
-- ============================================

/-- **Automated Incorrectness Logic prover for loop-free programs.**

  Strategy:
  1. Reduce IL triple to VC via `vc_sound`
  2. Unfold SP definitions
  3. Convert `∃ s : State` to `∃ v : Nat` via `sp_assign_elim`
  4. Simplify state accesses via `simp_all [State.update]`
  5. Close arithmetic with `omega`

  Handles: skip, assign, seq, assume, assert, if-then-else.
  Does NOT handle while loops (use `il_vc_while` or `vc_while_inv_sound`). -/
elab "incorrectness_auto" : tactic => do
  -- Phase 1: Reduce IL triple to verification condition
  evalTactic (← `(tactic| apply vc_sound))
  evalTactic (← `(tactic| intro _ _))
  -- Try exact match before any rewriting (handles q = sp c p)
  try evalTactic (← `(tactic| assumption))
  catch _ =>
  -- Phase 2: Unfold SP to Nat-existential form (sp_assign_nat is the key)
  evalTactic (← `(tactic| simp only [sp_skip', sp_assign_nat, sp_seq',
                           sp_ite', sp_assume', sp_assert']))
  -- Phase 3: Simplify state accesses + eliminate existentials + close
  evalTactic (← `(tactic| first
    | (simp_all (config := { decide := true })
        [State.update, exists_nat_const, exists_nat_eq_and, exists_nat_and_eq,
         exists_nat_eq_and', exists_nat_and_eq',
         exists_and_eq_add, exists_and_add_eq]
       <;> try omega)
    | (left
       simp_all (config := { decide := true })
        [State.update, exists_nat_const, exists_nat_eq_and, exists_nat_and_eq,
         exists_nat_eq_and', exists_nat_and_eq',
         exists_and_eq_add, exists_and_add_eq]
       <;> try omega)
    | (right
       simp_all (config := { decide := true })
        [State.update, exists_nat_const, exists_nat_eq_and, exists_nat_and_eq,
         exists_nat_eq_and', exists_nat_and_eq',
         exists_and_eq_add, exists_and_add_eq]
       <;> try omega)))
