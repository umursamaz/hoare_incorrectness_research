import Language
import AExp

namespace Language

-- Predicate Expressions (Boolean expressions over arithmetic)
inductive PExp : Type where
  | true  : PExp                    -- ⊤
  | false : PExp                    -- ⊥
  | eq    : AExp → AExp → PExp      -- e₁ = e₂
  | lt    : AExp → AExp → PExp      -- e₁ < e₂
  | le    : AExp → AExp → PExp      -- e₁ ≤ e₂
  | gt    : AExp → AExp → PExp      -- e₁ > e₂
  | ge    : AExp → AExp → PExp      -- e₁ ≥ e₂
  | not   : PExp → PExp             -- ¬p
  | and   : PExp → PExp → PExp      -- p ∧ q
  | or    : PExp → PExp → PExp      -- p ∨ q

-- PExp evaluation: PExp → State → Prop
def PExp.eval (p : PExp) (s : State) : Prop :=
  match p with
  | .true => True
  | .false => False
  | .eq e₁ e₂ => e₁.eval s = e₂.eval s
  | .lt e₁ e₂ => e₁.eval s < e₂.eval s
  | .le e₁ e₂ => e₁.eval s ≤ e₂.eval s
  | .gt e₁ e₂ => e₁.eval s > e₂.eval s
  | .ge e₁ e₂ => e₁.eval s ≥ e₂.eval s
  | .not p => ¬(p.eval s)
  | .and p q => p.eval s ∧ q.eval s
  | .or p q => p.eval s ∨ q.eval s


def PExp.subst (p : PExp) (x : String) (a : AExp) : PExp :=
  match p with
  | .true => .true
  | .false => .false
  | .eq e₁ e₂ => .eq (e₁.subst x a) (e₂.subst x a)
  | .lt e₁ e₂ => .lt (e₁.subst x a) (e₂.subst x a)
  | .le e₁ e₂ => .le (e₁.subst x a) (e₂.subst x a)
  | .gt e₁ e₂ => .gt (e₁.subst x a) (e₂.subst x a)
  | .ge e₁ e₂ => .ge (e₁.subst x a) (e₂.subst x a)
  | .not p => .not (p.subst x a)
  | .and p q => .and (p.subst x a) (q.subst x a)
  | .or p q => .or (p.subst x a) (q.subst x a)

theorem PExp.subst_lemma (p : PExp) (a : AExp) (x : String) (s : State) :
    (p.subst x a).eval s ↔ p.eval (s[x ↦ a.eval s]) := by
  induction p with
  | true => simp [PExp.subst, PExp.eval]
  | false => simp [PExp.subst, PExp.eval]
  | eq e₁ e₂ =>
    simp [PExp.subst, PExp.eval, AExp.subst_lemma]
  | lt e₁ e₂ =>
    simp [PExp.subst, PExp.eval, AExp.subst_lemma]
  | le e₁ e₂ =>
    simp [PExp.subst, PExp.eval, AExp.subst_lemma]
  | gt e₁ e₂ =>
    simp [PExp.subst, PExp.eval, AExp.subst_lemma]
  | ge e₁ e₂ =>
    simp [PExp.subst, PExp.eval, AExp.subst_lemma]
  | not p ih =>
    simp [PExp.subst, PExp.eval, ih]
  | and p q ihp ihq =>
    simp [PExp.subst, PExp.eval, ihp, ihq]
  | or p q ihp ihq =>
    simp [PExp.subst, PExp.eval, ihp, ihq]

end Language
