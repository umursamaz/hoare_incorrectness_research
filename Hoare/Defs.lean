import Hoare.Language
namespace Hoare

-- Partial Correctness Hoare Triple Definition
-- {P} S {Q} holds if whenever we start in a state satisfying P,
-- and S terminates, the resulting state satisfies Q.
def PartialHoare (P : State → Prop)
        (S : Stmt)
        (Q : State → Prop) : Prop :=
  ∀ s t, P s → (S, s) ⟹ t → Q t

def IncorrectnessHoare (P : State → Prop)
        (S : Stmt)
        (Q : State → Prop) : Prop :=
  ∀ t, Q t → ∃ s, P s ∧ (S, s) ⟹ t


-- Syntactic Sugar (Notation from page 142)
-- Allows writing {* P *} (S) {* Q *}
notation "{* " P " *} " "(" S ")" " {* " Q " *}"
  => PartialHoare P S Q

notation "[* " P " *] " "(" S ")" " [* " Q " *]"
  => IncorrectnessHoare P S Q

end Hoare
