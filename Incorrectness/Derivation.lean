import Incorrectness.Skip
import Incorrectness.Assign
import Incorrectness.Seq
import Incorrectness.If
import Incorrectness.While
import Incorrectness.Assert
import Incorrectness.Assume
import Incorrectness.Cons
import Incorrectness.Frame

open Language
namespace Incorrectness

/-!
# Derivation Trees for Incorrectness Logic

This file defines an inductive `Derivation` type that represents
syntactic proof trees (derivations) for IL triples, with one
constructor per inference rule from O'Hearn (2020).

The main result is the **soundness meta-theorem**:

  `Derivation P S Q → [* P *] (S) [* Q *]`

which states that every syntactically derivable IL triple is
semantically valid.
-/

-- ============================================
-- Derivation Inductive Type
-- ============================================

/-- Syntactic derivation trees for Incorrectness Logic.

    Each constructor mirrors one inference rule. A term of type
    `Derivation P S Q` is a finite proof tree witnessing that
    the triple `[P] S [Q]` is derivable from the IL rules. -/
inductive Derivation : (State → Prop) → Stmt → (State → Prop) → Prop where

  /-- **Skip**: `[P] skip [P]` -/
  | skip {P : State → Prop} :
      Derivation P Stmt.skip P

  /-- **Assignment** (Floyd forward axiom):
      `[P] x := a [∃ s, P s ∧ t = s[x ↦ a s]]` -/
  | assign {P : State → Prop} {x : String} {a : State → Nat} :
      Derivation P (Stmt.assign x a) (fun t => ∃ s, P s ∧ t = s[x ↦ a s])

  /-- **Sequencing**: from `[P] S₁ [Q]` and `[Q] S₂ [R]`,
      derive `[P] S₁;S₂ [R]` -/
  | seq {P Q R : State → Prop} {S1 S2 : Stmt} :
      Derivation P S1 Q →
      Derivation Q S2 R →
      Derivation P (Stmt.seq S1 S2) R

  /-- **If-true branch**: from `[P ∧ B] S₁ [Q]`,
      derive `[P] if B then S₁ else S₂ [Q]` -/
  | if_then {P Q : State → Prop} {B : State → Prop} {S1 S2 : Stmt} :
      Derivation (fun s => P s ∧ B s) S1 Q →
      Derivation P (Stmt.ifThenElse B S1 S2) Q

  /-- **If-false branch**: from `[P ∧ ¬B] S₂ [Q]`,
      derive `[P] if B then S₁ else S₂ [Q]` -/
  | if_else {P Q : State → Prop} {B : State → Prop} {S1 S2 : Stmt} :
      Derivation (fun s => P s ∧ ¬B s) S2 Q →
      Derivation P (Stmt.ifThenElse B S1 S2) Q

  /-- **While (zero iterations)**: `[P] while B do S [P ∧ ¬B]` -/
  | while_zero {P : State → Prop} {B : State → Prop} {S : Stmt} :
      Derivation P (Stmt.whileDo B S) (fun t => P t ∧ ¬B t)

  /-- **While (iteration rule)** with indexed invariant:
      from `∀ i, [Inv(i) ∧ B] S [Inv(i+1)]`,
      derive `[Inv(0)] while B do S [¬B ∧ ∃ i, Inv(i)]` -/
  | while_iter {Inv : Nat → State → Prop} {B : State → Prop} {S : Stmt} :
      (∀ i, Derivation (fun s => Inv i s ∧ B s) S (Inv (i + 1))) →
      Derivation (Inv 0) (Stmt.whileDo B S) (fun t => ¬B t ∧ ∃ i, Inv i t)

  /-- **Assert-ok**: `[P ∧ B] assert(B) [P ∧ B]` -/
  | assert_ok {P B : State → Prop} :
      Derivation (fun s => P s ∧ B s) (Stmt.assert B) (fun s => P s ∧ B s)

  /-- **Assert-error**: `[P ∧ ¬B] assert(B) [P ∧ ¬B]` -/
  | assert_er {P B : State → Prop} :
      Derivation (fun s => P s ∧ ¬B s) (Stmt.assert B) (fun s => P s ∧ ¬B s)

  /-- **Assert** (combined ok + error, uses classical logic):
      `[P] assert(B) [P]` -/
  | assert {P B : State → Prop} :
      Derivation P (Stmt.assert B) P

  /-- **Assume**: `[P ∧ B] assume(B) [P ∧ B]` -/
  | assume {P B : State → Prop} :
      Derivation (fun s => P s ∧ B s) (Stmt.assume B) (fun s => P s ∧ B s)

  /-- **Consequence** (weakening):
      from `P' ⊆ P`, `[P'] S [Q']`, and `Q ⊆ Q'`,
      derive `[P] S [Q]` -/
  | consequence {P P' Q Q' : State → Prop} {S : Stmt} :
      (∀ s, P' s → P s) →
      Derivation P' S Q' →
      (∀ s, Q s → Q' s) →
      Derivation P S Q

  /-- **Frame rule**:
      from `[P] S [Q]` and R backwards-preserved by S,
      derive `[P ∧ R] S [Q ∧ R]` -/
  | frame {P Q R : State → Prop} {S : Stmt} :
      Derivation P S Q →
      (∀ s t, R t → (S, s) ⟹ t → R s) →
      Derivation (fun s => P s ∧ R s) S (fun t => Q t ∧ R t)

-- ============================================
-- Soundness Meta-Theorem
-- ============================================

/-- **Soundness Meta-Theorem.**

    Every syntactically derivable IL triple is semantically valid.
    That is, if `Derivation P S Q` can be constructed, then the
    semantic triple `[* P *] (S) [* Q *]` holds.

    Proof by structural induction on the derivation tree, delegating
    each case to the corresponding semantic soundness theorem. -/
theorem soundness {P : State → Prop} {S : Stmt} {Q : State → Prop}
    (d : Derivation P S Q) : [* P *] (S) [* Q *] := by
  induction d with
  | skip => exact skip_intro
  | assign => exact assign_intro
  | seq _ _ ih1 ih2 => exact seq_intro ih1 ih2
  | if_then _ ih => exact if_then ih
  | if_else _ ih => exact if_else ih
  | while_zero => exact while_intro
  | while_iter _ ih => exact while_intro_paper ih
  | assert_ok => exact assert_ok_intro
  | assert_er => exact assert_er_intro
  | assert => exact assert_intro
  | assume => exact assume_intro
  | consequence hP _ hQ ih => exact consequence hP ih hQ
  | frame _ hR ih => exact frame ih hR

end Incorrectness
