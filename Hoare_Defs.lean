import Language

-- Partial Correctness Hoare Triple Definition
-- {P} S {Q} holds if whenever we start in a state satisfying P,
-- and S terminates, the resulting state satisfies Q.
def PartialHoare (P : State → Prop)
        (S : Stmt)
        (Q : State → Prop) : Prop :=
  ∀ s t, P s → (S, s) ⟹ t → Q t

-- Syntactic Sugar (Notation from page 142)
-- Allows writing {* P *} (S) {* Q *}
notation "{* " P " *} " "(" S ")" " {* " Q " *}"
=> PartialHoare P S Q
