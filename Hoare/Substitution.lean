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


-- P' s → P t
-- Hem P hem e bir Aexp olsun. O şekilde ispatlamaya çalışayım. Bu kitaba göre ama.
-- Daha sonra P genişleyecek.
-- Kitabınkini modifiye etmek lazım. "Bir state in içinde x i e ile değiştirmek ne demek?"
-- Lemmada P nin içinde x i e olarak güncellemeyi tanımlamak lazım. Predicate içinde x in değerini değiştirmek ne demek?
-- P bir proposition olarak güncellenecek.
-- fun P[x ↦ e]
-- Predicate için syntax oluşturmak lazım. Predicate ı tanımlayacağım.
-- Aexp i genişletmeyeceğim, Aexp (22.sayfa) kullanan bir propositionlar tanımla.
-- İçine ∧ ∨ ¬ gibi operatorler ekleyebiliriz mesela.
-- Pexp eval tanımla. Hem int için hem bool için. Bool belki kalkabilir.
-- Alpha type kullanabiliriz.
-- Pexp ↦ prop döndüreceğiz.
--
