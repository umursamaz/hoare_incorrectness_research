import Hoare.Defs
open Language
namespace Hoare

theorem substitution_lemma {P : State → Prop}
    {x : String}
    {e : State → Nat}
    {s t : State}
    (h : t = s[x ↦ e s])
    : P (s[x ↦ e s]) → P t :=
  by
  intro hP
  -- rw [h]
  exact h ▸ hP


theorem assign_intro' {P : State → Prop}
    {x : String}
    {a : State → Nat} :
  {* fun s => P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  by
  intro s t hP hStep
  cases hStep
  exact substitution_lemma rfl hP

end Hoare
