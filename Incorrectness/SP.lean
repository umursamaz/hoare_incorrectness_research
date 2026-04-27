import Incorrectness.Defs
import Language

open Language
namespace Incorrectness

/-!
# Strongest Postcondition for Incorrectness Logic

This file implements a forward SP-based verification condition generator
for Incorrectness Logic. The key idea:

- `sp c p` computes the strongest postcondition of program `c`
  with respect to precondition `p`
- `sp_sound` proves that `sp` always yields a valid IL postcondition
- `vc_sound` shows that proving `q ⇒ sp(c, p)` suffices to establish `[p] c [q]`

This is the IL analogue of Hoare Logic's backward wp-based VC generation,
but running forwards (precondition → postcondition), which is the natural
direction for under-approximate reasoning (O'Hearn 2020, Proposition 8).
-/

-- ============================================
-- Helper lemmas for State updates
-- ============================================

/-- Updating a variable to its current value is identity -/
theorem state_update_same (s : State) (x : String) :
    s[x ↦ s x] = s := by
  funext y
  simp only [State.update]
  split
  · case isTrue h => rw [h]
  · case isFalse => rfl

/-- Double update on the same variable keeps only the last -/
theorem state_update_override (s : State) (x : String) (v1 v2 : Nat) :
    (s[x ↦ v1])[x ↦ v2] = s[x ↦ v2] := by
  funext y
  unfold State.update
  by_cases h : y = x <;> simp [h]

/-- If s x = v, then s[x ↦ v] = s -/
theorem state_update_id (s : State) (x : String) (v : Nat)
    (h : s x = v) : s[x ↦ v] = s := by
  rw [← h]; exact state_update_same s x

/-- Reading a freshly updated variable gives the new value -/
theorem state_update_eq (s : State) (x : String) (v : Nat) :
    (s[x ↦ v]) x = v := by
  simp [State.update]

/-- Reading a different variable after update gives the old value -/
theorem state_update_neq (s : State) (x y : String) (v : Nat)
    (h : y ≠ x) : (s[x ↦ v]) y = s y := by
  simp [State.update, h]

-- ============================================
-- Strongest Postcondition Computation
-- ============================================

/-- Strongest postcondition for Incorrectness Logic.

  For each program construct, sp computes the exact set of reachable states:
  - skip: state unchanged
  - assign x a: Floyd's forward axiom (∃ old state)
  - seq: compose sp's
  - if: disjunction of branches
  - assume B: filter by B
  - assert B: state unchanged (both ok/er paths preserve state)
  - while B S: states reachable from p via the loop's big-step semantics

  The while clause is the *semantic* SP: the exact reachability set defined
  via BigStep. This makes `sp` an honest specification for every construct
  (no `False` placeholder). To discharge a while VC in practice, use the
  helper theorems in `Incorrectness.While` (`vc_while_sound` for bounded
  unrolling, `vc_while_inv_sound` for indexed invariant), which produce the
  IL triple directly without ever needing to compute this clause symbolically. -/
def sp (c : Stmt) (p : State → Prop) : State → Prop :=
  match c with
  | Stmt.skip => p
  | Stmt.assign x a => fun t => ∃ s, p s ∧ t = s[x ↦ a s]
  | Stmt.seq c1 c2 => sp c2 (sp c1 p)
  | Stmt.ifThenElse b c1 c2 =>
      fun t => sp c1 (fun s => p s ∧ b s) t
             ∨ sp c2 (fun s => p s ∧ ¬b s) t
  | Stmt.assume B => fun s => p s ∧ B s
  | Stmt.assert _ => p
  | Stmt.whileDo B S => fun t => ∃ s, p s ∧ (Stmt.whileDo B S, s) ⟹ t

-- Simp lemmas for unfolding sp in proofs
@[simp] theorem sp_skip' : sp Stmt.skip p = p := rfl

@[simp] theorem sp_assign' :
    sp (Stmt.assign x a) p = fun t => ∃ s, p s ∧ t = s[x ↦ a s] := rfl

@[simp] theorem sp_seq' :
    sp (Stmt.seq c1 c2) p = sp c2 (sp c1 p) := rfl

@[simp] theorem sp_ite' :
    sp (Stmt.ifThenElse b c1 c2) p
    = fun t => sp c1 (fun s => p s ∧ b s) t
             ∨ sp c2 (fun s => p s ∧ ¬b s) t := rfl

@[simp] theorem sp_assume' :
    sp (Stmt.assume B) p = fun s => p s ∧ B s := rfl

@[simp] theorem sp_assert' :
    sp (Stmt.assert B) p = p := rfl

@[simp] theorem sp_whileDo' :
    sp (Stmt.whileDo B S) p
    = fun t => ∃ s, p s ∧ (Stmt.whileDo B S, s) ⟹ t := rfl

-- ============================================
-- SP Assignment Elimination (for automation)
-- ============================================

/-- **Key reformulation for automation.**
  Converts existential over `State` to existential over `Nat`:
  - LHS: `∃ s : State, p s ∧ t = s[x ↦ a s]`  (hard to solve: need full state witness)
  - RHS: `∃ v : Nat, p(t[x↦v]) ∧ t x = a(t[x↦v])`  (easy: just find old value of x)

  After `simp [State.update]`, RHS becomes pure Nat arithmetic that
  `simp_all` + `omega` can close automatically. -/
theorem sp_assign_elim {p : State → Prop} {x : String} {a : State → Nat} {t : State} :
    (∃ s, p s ∧ t = s[x ↦ a s]) ↔ ∃ v, p (t[x ↦ v]) ∧ t x = a (t[x ↦ v]) := by
  constructor
  · rintro ⟨s, hp, heq⟩
    subst heq
    refine ⟨s x, ?_, ?_⟩
    · rwa [state_update_override, state_update_same]
    · simp only [state_update_eq, state_update_override, state_update_same]
  · rintro ⟨v, hp, heq⟩
    exact ⟨t[x ↦ v], hp, by
      funext _y; simp only [State.update]; split <;> simp_all⟩

/-- Direct simp lemma: unfolds `sp (assign x a) p` to Nat-existential form.
    Use this INSTEAD of `sp_assign'` in automation — avoids the intermediate
    `∃ s : State` form that's hard for `simp_all` to close. -/
@[simp] theorem sp_assign_nat {p : State → Prop} {x : String} {a : State → Nat} :
    sp (Stmt.assign x a) p = fun t => ∃ v, p (t[x ↦ v]) ∧ t x = a (t[x ↦ v]) := by
  funext t; exact propext sp_assign_elim

-- Helper lemmas: eliminate `∃ v : Nat` in various forms

theorem exists_nat_const {p : Prop} : (∃ _ : Nat, p) ↔ p :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

-- Eliminate when v is determined by an equation
theorem exists_nat_eq_and {p : Nat → Prop} {a : Nat} :
    (∃ v, v = a ∧ p v) ↔ p a := ⟨fun ⟨_, rfl, hp⟩ => hp, fun hp => ⟨a, rfl, hp⟩⟩

theorem exists_nat_and_eq {p : Nat → Prop} {a : Nat} :
    (∃ v, p v ∧ v = a) ↔ p a := ⟨fun ⟨_, hp, rfl⟩ => hp, fun hp => ⟨a, hp, rfl⟩⟩

theorem exists_nat_eq_and' {p : Nat → Prop} {a : Nat} :
    (∃ v, a = v ∧ p v) ↔ p a := ⟨fun ⟨_, rfl, hp⟩ => hp, fun hp => ⟨a, rfl, hp⟩⟩

theorem exists_nat_and_eq' {p : Nat → Prop} {a : Nat} :
    (∃ v, p v ∧ a = v) ↔ p a := ⟨fun ⟨_, hp, rfl⟩ => hp, fun hp => ⟨a, hp, rfl⟩⟩

-- Eliminate when v appears in v + k (common from x := x + 1)
theorem exists_and_eq_add {p : Nat → Prop} {n k : Nat} :
    (∃ v, p v ∧ n = v + k) ↔ n ≥ k ∧ p (n - k) := by
  constructor
  · rintro ⟨v, hp, heq⟩
    exact ⟨by omega, by rwa [show n - k = v from by omega]⟩
  · rintro ⟨hge, hp⟩
    exact ⟨n - k, hp, by omega⟩

theorem exists_and_add_eq {p : Nat → Prop} {n k : Nat} :
    (∃ v, p v ∧ v + k = n) ↔ n ≥ k ∧ p (n - k) := by
  constructor
  · rintro ⟨v, hp, heq⟩
    exact ⟨by omega, by rwa [show n - k = v from by omega]⟩
  · rintro ⟨hge, hp⟩
    exact ⟨n - k, hp, by omega⟩

-- ============================================
-- Soundness Theorem
-- ============================================

/-- **Core Soundness Theorem.**

  For any program c and precondition p, sp(c, p) is a valid
  IL postcondition. That is, every state in sp(c, p) is
  reachable from some state satisfying p.

  Formally: `[* p *] (c) [* sp c p *]`

  This is proved by structural induction on c. -/
theorem sp_sound (c : Stmt) (p : State → Prop) :
    [* p *] (c) [* sp c p *] := by
  induction c generalizing p with
  | skip =>
    -- sp skip p = p
    -- Need: ∀ t, p t → ∃ s, p s ∧ (skip, s) ⟹ t
    intro t hp
    exact ⟨t, hp, BigStep.skip t⟩

  | assign x a =>
    -- sp (assign x a) p = fun t => ∃ s, p s ∧ t = s[x ↦ a s]
    -- Need: ∀ t, (∃ s, p s ∧ t = s[x ↦ a s]) → ∃ s, p s ∧ (assign x a, s) ⟹ t
    intro t ⟨s, hp, heq⟩
    exact ⟨s, hp, heq ▸ BigStep.assign x a s⟩

  | seq c1 c2 ih1 ih2 =>
    -- sp (c1; c2) p = sp c2 (sp c1 p)
    -- IH1: ∀ p, [* p *] (c1) [* sp c1 p *]
    -- IH2: ∀ p, [* p *] (c2) [* sp c2 p *]
    intro t hsp
    -- hsp : sp c2 (sp c1 p) t
    -- By IH2: ∃ mid, sp c1 p mid ∧ (c2, mid) ⟹ t
    obtain ⟨mid, hmid, hc2⟩ := ih2 (sp c1 p) t hsp
    -- By IH1: ∃ s, p s ∧ (c1, s) ⟹ mid
    obtain ⟨s, hp, hc1⟩ := ih1 p mid hmid
    -- Combine with BigStep.seq
    exact ⟨s, hp, BigStep.seq c1 c2 s mid t hc1 hc2⟩

  | ifThenElse b c1 c2 ih1 ih2 =>
    -- sp (if b c1 c2) p = sp c1 (p ∧ b) ∨ sp c2 (p ∧ ¬b)
    intro t hsp
    cases hsp with
    | inl h1 =>
      -- Came from true branch
      obtain ⟨s, ⟨hp, hb⟩, hc1⟩ := ih1 (fun s => p s ∧ b s) t h1
      exact ⟨s, hp, BigStep.if_true b c1 c2 s t hb hc1⟩
    | inr h2 =>
      -- Came from false branch
      obtain ⟨s, ⟨hp, hnb⟩, hc2⟩ := ih2 (fun s => p s ∧ ¬b s) t h2
      exact ⟨s, hp, BigStep.if_false b c1 c2 s t hnb hc2⟩

  | assume B =>
    -- sp (assume B) p = fun s => p s ∧ B s
    intro t ⟨hp, hb⟩
    exact ⟨t, hp, BigStep.assume B t hb⟩

  | assert B =>
    -- sp (assert B) p = p
    -- assert preserves state regardless of B
    intro t hp
    cases Classical.em (B t) with
    | inl hb  => exact ⟨t, hp, BigStep.assert_ok B t hb⟩
    | inr hnb => exact ⟨t, hp, BigStep.assert_er B t hnb⟩

  | whileDo b c _ih =>
    -- sp (while b c) p t = ∃ s, p s ∧ (while b c, s) ⟹ t
    -- The IL triple goal unfolds to the same shape, so the witness is direct.
    intro t ⟨s, hp, hexec⟩
    exact ⟨s, hp, hexec⟩

-- ============================================
-- VC Soundness (Main User-Facing Theorem)
-- ============================================

/-- **Verification Condition Soundness.**

  If the verification condition `∀ t, q t → sp c p t` is provable,
  then the IL triple `[* p *] (c) [* q *]` holds.

  This is the main theorem connecting VC generation to IL validity.
  The workflow is:
  1. User provides [p] c [q]
  2. System computes sp(c, p)
  3. User (or tactic) proves q ⇒ sp(c, p)
  4. vc_sound gives the IL triple

  Analogy to Hoare Logic:
  - Hoare VC: p ⇒ wp(c, q)   "precondition implies weakest precondition"
  - IL VC:    q ⇒ sp(c, p)   "result implies strongest postcondition" -/
theorem vc_sound {c : Stmt} {p q : State → Prop}
    (hvc : ∀ t, q t → sp c p t) :
    [* p *] (c) [* q *] := by
  intro t hq
  exact sp_sound c p t (hvc t hq)

end Incorrectness
