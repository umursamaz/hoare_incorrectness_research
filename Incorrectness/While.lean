import Incorrectness.Defs
import Incorrectness.Cons
import Incorrectness.SP
open Language
namespace Incorrectness

/-!
# While Loops in Incorrectness Logic

This file consolidates *all* reasoning about while loops:

1. **Pure semantic IL theorems** — direct proofs from the IL definition
   - `while_intro`           : zero-iteration rule
   - `while_intro_paper`     : indexed-invariant rule (O'Hearn's
                                Backwards Variant ≡ de Vries's While rule)

2. **Bounded unrolling** — operational approach: unfold the loop k times
   - `unroll_while`          : syntactic k-step unrolling
   - `unroll_bigstep`        : an unrolled execution is also a loop execution
   - `unroll_sound`          : IL triple for unrolled ⇒ IL triple for loop
   - `vc_while_sound`        : combined SP-based VC for unrolling

3. **Invariant-based VC** — composes consequence + indexed invariant + sp
   - `vc_while_inv_sound`    : main theorem for invariant-style proofs
-/

-- =============================================================
-- Section 1. Pure semantic IL theorems
-- =============================================================

/-- **Zero-iteration rule.**

  `[P] while B do S [P ∧ ¬B]`

  The trivial case: every state satisfying both P and ¬B is reachable
  from itself via the loop (taking zero iterations). -/
theorem while_intro
    {P : State → Prop}
    {B : State → Prop}
    {S : Stmt} :
    [* P *] (Stmt.whileDo B S) [* fun t => P t ∧ ¬B t *] := by
  intro t ⟨hP, hNotB⟩
  exact ⟨t, hP, BigStep.while_false B S t hNotB⟩

/-- Helper for `while_intro_paper`.

  Given that the body preserves an indexed invariant
  (`P i ∧ B → S → P (i+1)`), any execution of the loop starting from a
  state satisfying `P n` can be extended backwards through `n` body
  iterations to a state satisfying `P 0`. -/
theorem while_iterations_aux
    {P : Nat → State → Prop}
    {B : State → Prop}
    {S : Stmt}
    (hBody : ∀ i, [* fun s => P i s ∧ B s *] (S) [* fun s => P (i + 1) s *]) :
    ∀ n sn t,
      P n sn →
      (Stmt.whileDo B S, sn) ⟹ t →
      ∃ s0, P 0 s0 ∧ (Stmt.whileDo B S, s0) ⟹ t := by
  intro n
  induction n with
  | zero =>
    intro s0 t hP0 hExec
    exact ⟨s0, hP0, hExec⟩
  | succ n ih =>
    intro sn1 t hPsucc hExec
    obtain ⟨sn, ⟨hPn, hBsn⟩, hStepS⟩ := hBody n sn1 hPsucc
    exact ih sn t hPn (BigStep.while_true B S sn sn1 t hBsn hStepS hExec)

/-- **Indexed-invariant rule** (O'Hearn's Backwards Variant ≡ de Vries's While).

      ∀ i. [P i ∧ B] S [P (i+1)]
   ────────────────────────────────────
   [P 0] while B do S [¬B ∧ ∃ i. P i]

  The user provides a family `P : Nat → State → Prop` indexed by the
  iteration count. If body S takes states from `P i` to `P (i+1)` (under
  the loop guard), then any exit state from the loop is reachable from
  `P 0` after some number of iterations. -/
theorem while_intro_paper
    {P : Nat → State → Prop}
    {B : State → Prop}
    {S : Stmt}
    (hBody : ∀ i, [* fun s => P i s ∧ B s *] (S) [* fun s => P (i + 1) s *]) :
    [* P 0 *] (Stmt.whileDo B S) [* fun t => ¬B t ∧ ∃ i, P i t *] := by
  intro t ⟨hNotB, ⟨i, hPi⟩⟩
  exact while_iterations_aux hBody i t t hPi (BigStep.while_false B S t hNotB)

-- =============================================================
-- Section 2. Bounded unrolling
-- =============================================================

/-- Unroll a while loop `k` times into a finite (loop-free) statement.

  - `unroll_while b c 0       = assume(¬b)`              (exit immediately)
  - `unroll_while b c (k+1)   = if b then (c; unroll k) else skip`

  The intuition: any execution of `unroll_while b c k` is one possible
  execution of `while b do c` that takes at most `k` iterations. -/
def unroll_while (b : State → Prop) (c : Stmt) : Nat → Stmt
  | 0     => Stmt.assume (fun s => ¬ b s)
  | n + 1 => Stmt.ifThenElse b
              (Stmt.seq c (unroll_while b c n))
              Stmt.skip

/-- Every big-step execution of `unroll_while b c k` corresponds to a
    big-step execution of the actual `while b do c`. By induction on `k`. -/
theorem unroll_bigstep (b : State → Prop) (c : Stmt) :
    ∀ k s t, (unroll_while b c k, s) ⟹ t → (Stmt.whileDo b c, s) ⟹ t := by
  intro k
  induction k with
  | zero =>
    intro s t h
    -- unroll_while b c 0 = assume(¬b), so h forces ¬b s and t = s
    cases h with
    | assume _ _ hcond => exact BigStep.while_false b c s hcond
  | succ k ih =>
    intro s t h
    -- unroll_while b c (k+1) = if b then (c; unroll k) else skip
    cases h with
    | if_true _ _ _ _ _ hcond hbody =>
      cases hbody with
      | seq _ _ _ mid _ hc hunroll =>
        exact BigStep.while_true b c s mid t hcond hc (ih mid t hunroll)
    | if_false _ _ _ _ _ hcond hbody =>
      cases hbody with
      | skip _ => exact BigStep.while_false b c s hcond

/-- **Transfer theorem.** An IL triple about the unrolled loop transfers
    to an IL triple about the actual while loop. -/
theorem unroll_sound (b : State → Prop) (c : Stmt) (k : Nat)
    (p q : State → Prop)
    (h : [* p *] (unroll_while b c k) [* q *]) :
    [* p *] (Stmt.whileDo b c) [* q *] := by
  intro t hq
  obtain ⟨s, hp, hexec⟩ := h t hq
  exact ⟨s, hp, unroll_bigstep b c k s t hexec⟩

/-- **Combined VC + unrolling.**

  To prove `[P] while b do c [Q]` it suffices to prove the (loop-free)
  VC `q ⇒ sp(unroll_k, p)` for some `k`. This is O'Hearn's Derived
  Unrolling Rule cast as a VC. Best suited for loops with a small,
  *fixed* iteration count. For parametric loops use `vc_while_inv_sound`. -/
theorem vc_while_sound {b : State → Prop} {c : Stmt} {k : Nat}
    {p q : State → Prop}
    (hvc : ∀ t, q t → sp (unroll_while b c k) p t) :
    [* p *] (Stmt.whileDo b c) [* q *] := by
  apply unroll_sound b c k p q
  exact vc_sound hvc

-- =============================================================
-- Section 3. Invariant-based VC
-- =============================================================

/-- **Invariant-based VC for while loops.**

  The user provides an indexed invariant `Inv : Nat → State → Prop` and
  proves three (loop-free) verification conditions:

  1. `hPre`  : `Inv 0 ⊆ P`                              (initial state covered)
  2. `hBody` : `∀ i. Inv(i+1) ⇒ sp(S, Inv i ∧ B)`      (body preserves Inv)
  3. `hPost` : `Q ⊆ ¬B ∧ ∃ i. Inv i`                    (exit covers Q)

  This is the *user-facing* form of `while_intro_paper`: it composes the
  consequence rule with the indexed invariant rule and `vc_sound`.

  **Advantage over `vc_while_sound`**: proof size is *constant* in the
  number of iterations, and parametric bounds (e.g. `while x < n`) are
  expressible. -/
theorem vc_while_inv_sound
    {B : State → Prop} {S : Stmt}
    {P Q : State → Prop} {Inv : Nat → State → Prop}
    (hPre  : ∀ s, Inv 0 s → P s)
    (hBody : ∀ i, ∀ t, Inv (i + 1) t → sp S (fun s => Inv i s ∧ B s) t)
    (hPost : ∀ t, Q t → ¬B t ∧ ∃ i, Inv i t) :
    [* P *] (Stmt.whileDo B S) [* Q *] :=
  consequence hPre (while_intro_paper (fun i => vc_sound (hBody i))) hPost

end Incorrectness
