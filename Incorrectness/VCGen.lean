import Incorrectness.SP
import Incorrectness.While

open Language
open Incorrectness
open Lean Elab Tactic

-- ============================================
-- Nat-Existential Elimination Lemmas
-- ============================================
-- These are the simp-set used by `il_close` to eliminate the
-- `∃ v : Nat` quantifiers that emerge after `sp_assign_nat` is
-- applied and `State.update` is unfolded. They are pure logical
-- lemmas about `∃ v : Nat`, independent of any SP machinery.

namespace Incorrectness

/-- Trivial elimination: an unused Nat existential is the body itself. -/
theorem exists_nat_const {p : Prop} : (∃ _ : Nat, p) ↔ p :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

/-- Eliminate when `v` is determined by an equation `v = a`. -/
theorem exists_nat_eq_and {p : Nat → Prop} {a : Nat} :
    (∃ v, v = a ∧ p v) ↔ p a := ⟨fun ⟨_, rfl, hp⟩ => hp, fun hp => ⟨a, rfl, hp⟩⟩

theorem exists_nat_and_eq {p : Nat → Prop} {a : Nat} :
    (∃ v, p v ∧ v = a) ↔ p a := ⟨fun ⟨_, hp, rfl⟩ => hp, fun hp => ⟨a, hp, rfl⟩⟩

theorem exists_nat_eq_and' {p : Nat → Prop} {a : Nat} :
    (∃ v, a = v ∧ p v) ↔ p a := ⟨fun ⟨_, rfl, hp⟩ => hp, fun hp => ⟨a, rfl, hp⟩⟩

theorem exists_nat_and_eq' {p : Nat → Prop} {a : Nat} :
    (∃ v, p v ∧ a = v) ↔ p a := ⟨fun ⟨_, hp, rfl⟩ => hp, fun hp => ⟨a, hp, rfl⟩⟩

/-- Eliminate when `v` appears inside an addition (typical for `x := x + k`). -/
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

end Incorrectness

/-!
# VC Generation Tactics for Incorrectness Logic

This file provides Lean tactics that automate the repetitive parts
of VC-based IL proofs. The tactics are organized in dependency order
(helpers first, dispatchers last):

## Setup helpers (used by automation tactics below)
- `state_ext`        — proves state equalities by pointwise case analysis
- `il_vc`            — sets up a loop-free VC proof
- `il_vc_while`      — sets up a bounded-unrolling VC proof
- `il_close`         — closes a goal after SP unfolding (fast, AC-free)
- `il_close_ac`      — AC-normalising fallback: back-solves existentials whose
                       pinning equation is buried in a multi-clause invariant
- `il_close_hard`    — two-tier `first | il_close | il_close_ac`

## Specialized provers
- `incorrectness_auto_while N`        — bounded unrolling, explicit k
- `incorrectness_auto_while_search`   — bounded unrolling, k=1..10 search
- `incorrectness_auto_inv <inv>`      — invariant-hint, parametric loops
- `incorrectness_auto_inv_split N inv`— invariant-hint + iteration case-split

## Unified dispatcher (top-level entry point)
- `incorrectness_auto` — tries loop-free first, then bounded while search
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
-- Closing Helper: il_close
-- ============================================

/-- Atomic close: simp_all with our lemma set, then a search over up to
    three levels of `split` (for nested `if-then-else` in the goal), each
    followed by `omega`. The `done` guards ensure failure propagates so
    the caller's `first | ... | ...` enumeration can try alternatives. -/
elab "il_close_atom" : tactic => do
  evalTactic (← `(tactic|
    first
      | (simp_all (config := { decide := true })
          [State.update, exists_nat_const, exists_nat_eq_and, exists_nat_and_eq,
           exists_nat_eq_and', exists_nat_and_eq',
           exists_and_eq_add, exists_and_add_eq]
         <;> try omega
         all_goals done)
      | (simp_all (config := { decide := true })
          [State.update, exists_nat_const, exists_nat_eq_and, exists_nat_and_eq,
           exists_nat_eq_and', exists_nat_and_eq',
           exists_and_eq_add, exists_and_add_eq]
         <;> split
         <;> try omega
         all_goals done)
      | (simp_all (config := { decide := true })
          [State.update, exists_nat_const, exists_nat_eq_and, exists_nat_and_eq,
           exists_nat_eq_and', exists_nat_and_eq',
           exists_and_eq_add, exists_and_add_eq]
         <;> split <;> split
         <;> try omega
         all_goals done)
      | (simp_all (config := { decide := true })
          [State.update, exists_nat_const, exists_nat_eq_and, exists_nat_and_eq,
           exists_nat_eq_and', exists_nat_and_eq',
           exists_and_eq_add, exists_and_add_eq]
         <;> split <;> split <;> split
         <;> try omega
         all_goals done)))

/-- Reusable closer used after SP unfolding. Enumerates left/right paths
    through up to three levels of nested disjunctions (handles sequences
    of if-then-else and bounded-unrolling unfolds), trying `il_close_atom`
    at each leaf. -/
elab "il_close" : tactic => do
  evalTactic (← `(tactic| first
    | il_close_atom
    | (left; il_close_atom)
    | (right; il_close_atom)
    | (left; left; il_close_atom)
    | (left; right; il_close_atom)
    | (right; left; il_close_atom)
    | (right; right; il_close_atom)
    | (left; left; left; il_close_atom)
    | (left; left; right; il_close_atom)
    | (left; right; left; il_close_atom)
    | (left; right; right; il_close_atom)
    | (right; left; left; il_close_atom)
    | (right; left; right; il_close_atom)
    | (right; right; left; il_close_atom)
    | (right; right; right; il_close_atom)))

/-- **Heavyweight fallback closer.**

    AC-normalises `∧` (`and_assoc/and_comm/and_left_comm`) so a determining
    equation `v = c` buried deep inside a multi-clause invariant floats next
    to its binding `∃`, letting `exists_eq_*'` eliminate the witness. This is
    what a *cheap* `simp_all` cannot do: it only matches top-level `v = c`
    conjuncts. Needed for loop bodies with several simultaneous existentials
    over pinned variables (e.g. `prev := curr; curr := next curr`).

    AC-normalisation is deliberately kept OUT of `il_close_atom`: run on every
    leaf it explodes large invariants (the array example times out). It is a
    fallback, invoked by `il_close_hard` only after the cheap path fails. -/
elab "il_close_ac" : tactic => do
  evalTactic (← `(tactic|
    first
      | (simp_all (config := { decide := true })
          [State.update, exists_nat_const, exists_nat_eq_and, exists_nat_and_eq,
           exists_nat_eq_and', exists_nat_and_eq', exists_and_eq_add, exists_and_add_eq,
           and_assoc, and_comm, and_left_comm, exists_eq_left', exists_eq_right']
         <;> try omega
         all_goals done)
      | (simp_all (config := { decide := true })
          [State.update, exists_nat_const, exists_nat_eq_and, exists_nat_and_eq,
           exists_nat_eq_and', exists_nat_and_eq', exists_and_eq_add, exists_and_add_eq,
           and_assoc, and_comm, and_left_comm, exists_eq_left', exists_eq_right']
         <;> split
         <;> try omega
         all_goals done)))

/-- **Two-tier closer.** Try the fast, AC-free `il_close` first; fall back to
    the AC-heavy `il_close_ac` only when the cheap path fails. Used at the
    leaves of the iteration case-split, where buried existentials arise. This
    keeps the common case fast while extending coverage to pointer/array
    bodies that need witness back-solving from a multi-clause invariant. -/
elab "il_close_hard" : tactic => do
  evalTactic (← `(tactic| first | il_close | il_close_ac))

-- ============================================
-- Bounded While Automation
-- ============================================

/-- **Bounded while auto with explicit k.**

  `incorrectness_auto_while N` proves an IL triple of the form
  `[P] while B do S [Q]` by unrolling the loop exactly `N` times,
  unfolding all SP definitions, and closing with `il_close`.

  Use this when you know the maximum iteration count statically
  (analogous to a fixed-bound C `for` loop).

  Example: `[x = 0] while x < 3 do x := x+1 [x = 3]` is closed by
  `incorrectness_auto_while 3`. -/
syntax "incorrectness_auto_while" num : tactic
elab_rules : tactic
  | `(tactic| incorrectness_auto_while $k) => do
    evalTactic (← `(tactic| apply vc_while_sound (k := $k)))
    evalTactic (← `(tactic| intro _ _))
    evalTactic (← `(tactic| simp only [unroll_while, sp_skip', sp_assign_nat,
                             sp_seq', sp_ite', sp_assume', sp_assert']))
    evalTactic (← `(tactic| il_close))

/-- **Bounded while auto with k-search (1..10).**

  `incorrectness_auto_while_search` tries `incorrectness_auto_while N`
  for `N = 0, 1, 2, ..., 10` and uses the first one that succeeds.

  Use when you don't want to specify the bound manually. Cost: at most
  11 attempts; most fail fast. -/
elab "incorrectness_auto_while_search" : tactic => do
  evalTactic (← `(tactic| first
    | incorrectness_auto_while 0
    | incorrectness_auto_while 1
    | incorrectness_auto_while 2
    | incorrectness_auto_while 3
    | incorrectness_auto_while 4
    | incorrectness_auto_while 5
    | incorrectness_auto_while 6
    | incorrectness_auto_while 7
    | incorrectness_auto_while 8
    | incorrectness_auto_while 9
    | incorrectness_auto_while 10))

-- ============================================
-- Unified Dispatcher: incorrectness_auto
-- ============================================

/-- **Automated Incorrectness Logic prover (unified).**

  This is the single top-level tactic users should reach for. It tries
  in order:

  1. **Loop-free path:** `apply vc_sound` + introduce hypotheses,
     then either `assumption` (when `Q` matches the SP exactly) or
     `simp` + `il_close` (the standard case for skip/assign/seq/if/
     assume/assert).
  2. **Bounded while path:** if the program contains a while loop,
     fall back to `incorrectness_auto_while_search` (k=0..10).

  For loops with a parametric or large bound, use
  `incorrectness_auto_inv <inv>` directly with a user-provided
  indexed invariant — that case requires human input and is not
  attempted by this dispatcher. -/
elab "incorrectness_auto_lf" : tactic => do
  evalTactic (← `(tactic| apply vc_sound))
  evalTactic (← `(tactic| intro _ _))
  evalTactic (← `(tactic| first
    | assumption
    | (simp only [sp_skip', sp_assign_nat, sp_seq',
                  sp_ite', sp_assume', sp_assert'];
       il_close)))

elab "incorrectness_auto" : tactic => do
  evalTactic (← `(tactic| first
    | incorrectness_auto_lf
    | incorrectness_auto_while_search))

-- ============================================
-- Invariant-Hint While Automation
-- ============================================

/-- **Invariant-hint while auto.**

  `incorrectness_auto_inv <invariant>` applies `vc_while_inv_sound`
  with the user-provided indexed invariant, then attempts to close
  the three resulting subgoals (hPre, hBody, hPost) using `il_close`.

  Use when the loop has a parametric or unknown bound, but you can
  describe it with an indexed invariant `Inv : Nat → State → Prop`.

  Example: `[x=0 ∧ n>0] while x<n do x:=x+1 [x=n ∧ n>0]` is closed by
  `incorrectness_auto_inv (fun i s => s "x" = i ∧ i ≤ s "n" ∧ s "n" > 0)`. -/
syntax "incorrectness_auto_inv" term : tactic
elab_rules : tactic
  | `(tactic| incorrectness_auto_inv $inv) => do
    evalTactic (← `(tactic| apply vc_while_inv_sound (Inv := $inv)))
    evalTactic (← `(tactic|
      all_goals (first
        | il_close_hard
        | (intro _ _;
           simp only [sp_skip', sp_assign_nat, sp_seq',
                      sp_ite', sp_assume', sp_assert'];
           il_close_hard)
        | (intro _ _ _;
           simp only [sp_skip', sp_assign_nat, sp_seq',
                      sp_ite', sp_assume', sp_assert'];
           il_close_hard))))

-- ============================================
-- Bounded Case-Split for hBody (handles if-then-else in loop guard)
-- ============================================

/-- Builds the nested `rcases Nat.lt_or_ge` chain that case-splits on
    `x ≤ bound`, producing one branch per possible value `k, k+1, ..., bound`
    and `il_close`-ing each. Used to parametrise `il_close_split_at` by an
    arbitrary user-supplied bound. -/
private partial def mkSplitTac (x : Ident) (k : Nat) (bound : Nat) :
    TacticM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  if k ≥ bound then
    `(tacticSeq|
        have hieq : $x = $(quote bound) := by omega
        subst hieq
        il_close_hard)
  else
    let inner ← mkSplitTac x (k+1) bound
    `(tacticSeq|
        rcases Nat.lt_or_ge $x $(quote (k+1)) with hcase | hcase
        · have hieq : $x = $(quote k) := by omega
          subst hieq
          il_close_hard
        · $inner)

/-- **Bounded case-split closer (parametric).**

    `il_close_split_at x N` case-splits on the Nat `x` for values
    `0, 1, ..., N` and closes each branch with `il_close`. The branch
    `x = N` assumes the caller has placed `x ≤ N` in context (otherwise
    that branch's `omega` will fail unless `il_close` resolves the goal
    by contradiction).

    The `first | il_close | …` wrapper means: try to close without splitting
    first; only fall back to the case-split if that fails. -/
syntax "il_close_split_at" ident num : tactic
elab_rules : tactic
  | `(tactic| il_close_split_at $x:ident $n:num) => do
    let splitTac ← mkSplitTac x 0 n.getNat
    evalTactic (← `(tactic| first | il_close | $splitTac))

/-- **Invariant-hint while auto with iteration case-split (parametric).**

  `incorrectness_auto_inv_split N inv` is like `incorrectness_auto_inv`,
  but when the body VC cannot close directly it case-splits on the
  iteration counter for values `0, 1, ..., N` and closes each case.
  Use this for loops whose guard contains an `if`-expression whose
  discriminant is the iteration counter (e.g. sorted-insert position
  search). `N` must be at least the loop's maximum iteration count
  permitted by the invariant.

  Use when `incorrectness_auto_inv` fails on a body containing an
  index-dependent match/if. -/
syntax "incorrectness_auto_inv_split" num term : tactic
elab_rules : tactic
  | `(tactic| incorrectness_auto_inv_split $n:num $inv:term) => do
    evalTactic (← `(tactic|
      (apply vc_while_inv_sound (Inv := $inv)
       all_goals (first
         | il_close
         | (intro _ _;
            simp only [sp_skip', sp_assign_nat, sp_seq',
                       sp_ite', sp_assume', sp_assert'];
            il_close)
         | (intro i _ _;
            simp only [sp_skip', sp_assign_nat, sp_seq',
                       sp_ite', sp_assume', sp_assert'];
            il_close_split_at i $n)))))
