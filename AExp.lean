import Language

namespace Language

-- Arithmetic Expressions
inductive AExp : Type where
  | num : Nat → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp

-- AExp evaluation
def AExp.eval (e : AExp) (s : State) : Nat :=
  match e with
  | .num n => n
  | .var x => s x
  | .add e₁ e₂ => e₁.eval s + e₂.eval s
  | .sub e₁ e₂ => e₁.eval s - e₂.eval s
  | .mul e₁ e₂ => e₁.eval s * e₂.eval s


def AExp.subst (e : AExp) (x : String) (a : AExp) : AExp :=
  match e with
  | .num n => .num n
  | .var y => if y = x then a else .var y
  | .add e₁ e₂ => .add (e₁.subst x a) (e₂.subst x a)
  | .sub e₁ e₂ => .sub (e₁.subst x a) (e₂.subst x a)
  | .mul e₁ e₂ => .mul (e₁.subst x a) (e₂.subst x a)

theorem AExp.subst_lemma (e a : AExp) (x : String) (s : State) :
    (e.subst x a).eval s = e.eval (s[x ↦ a.eval s]) := by
  induction e with
  | num n => simp [AExp.subst, AExp.eval]
  | var y =>
    simp only [AExp.subst, AExp.eval, State.update]
    split
    · case isTrue => rfl
    · case isFalse => rfl
  | add e₁ e₂ ih₁ ih₂ =>
    simp [AExp.subst, AExp.eval, ih₁, ih₂]
  | sub e₁ e₂ ih₁ ih₂ =>
    simp [AExp.subst, AExp.eval, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp [AExp.subst, AExp.eval, ih₁, ih₂]

end Language
