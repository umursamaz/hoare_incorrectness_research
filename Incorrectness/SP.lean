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
  - while: conservative False (use bounded unrolling separately) -/
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
  | Stmt.whileDo _ _ => fun _ => False

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
    -- sp (while b c) p = False (conservative)
    intro t hf
    exact False.elim hf

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

-- ============================================
-- Bounded Loop Unrolling (for while)
-- ============================================

/-- Unroll a while loop k times as a finite statement.
  unroll_while b c 0 = assume(¬b)                        (exit immediately)
  unroll_while b c (k+1) = if b then (c; unroll k) else skip  (one more iteration) -/
def unroll_while (b : State → Prop) (c : Stmt) : Nat → Stmt
  | 0 => Stmt.assume (fun s => ¬ b s)
  | n + 1 => Stmt.ifThenElse b
               (Stmt.seq c (unroll_while b c n))
               Stmt.skip

/-- SP for bounded loop unrolling.
  Computes the disjunction of sp's for 0, 1, ..., k iterations. -/
def sp_while_bounded (b : State → Prop) (c : Stmt)
    (p : State → Prop) (bound : Nat) : State → Prop :=
  match bound with
  | 0 => sp (unroll_while b c 0) p
  | n + 1 => fun t => sp_while_bounded b c p n t
                     ∨ sp (unroll_while b c (n + 1)) p t

-- ============================================
-- Bounded Loop Unrolling Soundness
-- ============================================

/-- Key lemma: any execution of unroll_while b c k corresponds to
    an actual execution of while b do c. Proved by induction on k. -/
theorem unroll_bigstep (b : State → Prop) (c : Stmt) :
    ∀ k s t, (unroll_while b c k, s) ⟹ t → (Stmt.whileDo b c, s) ⟹ t := by
  intro k
  induction k with
  | zero =>
    intro s t h
    -- unroll_while b c 0 = assume(¬b)
    -- So h : (assume(¬b), s) ⟹ t, meaning ¬b s and t = s
    cases h with
    | assume _ _ hcond => exact BigStep.while_false b c s hcond
  | succ k ih =>
    intro s t h
    -- unroll_while b c (k+1) = if b then (c; unroll k) else skip
    cases h with
    | if_true _ _ _ _ _ hcond hbody =>
      -- b s holds, hbody : (c; unroll k, s) ⟹ t
      cases hbody with
      | seq _ _ _ mid _ hc hunroll =>
        -- hc : (c, s) ⟹ mid, hunroll : (unroll k, mid) ⟹ t
        exact BigStep.while_true b c s mid t hcond hc (ih mid t hunroll)
    | if_false _ _ _ _ _ hcond hbody =>
      -- ¬b s, hbody : (skip, s) ⟹ t
      cases hbody with
      | skip _ => exact BigStep.while_false b c s hcond

/-- Transfer theorem: IL triples for unrolled loops transfer to the actual while loop.
    If we can prove [* p *] (unroll k) [* q *], then [* p *] (while b c) [* q *]. -/
theorem unroll_sound (b : State → Prop) (c : Stmt) (k : Nat)
    (p q : State → Prop)
    (h : [* p *] (unroll_while b c k) [* q *]) :
    [* p *] (Stmt.whileDo b c) [* q *] := by
  intro t hq
  obtain ⟨s, hp, hexec⟩ := h t hq
  exact ⟨s, hp, unroll_bigstep b c k s t hexec⟩

/-- Combined VC + unrolling: prove q ⇒ sp(unroll_k, p), get [* p *] while [* q *].
    This is the main user-facing theorem for while loops. -/
theorem vc_while_sound {b : State → Prop} {c : Stmt} {k : Nat}
    {p q : State → Prop}
    (hvc : ∀ t, q t → sp (unroll_while b c k) p t) :
    [* p *] (Stmt.whileDo b c) [* q *] := by
  apply unroll_sound b c k p q
  exact vc_sound hvc

end Incorrectness
