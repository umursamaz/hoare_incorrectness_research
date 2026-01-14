import Language
open Language
namespace Incorrectness

-- [P] S [Q] : Under-approximation
def IncorrectnessHoare (P : State → Prop)
        (S : Stmt)
        (Q : State → Prop) : Prop :=
  ∀ t, Q t → ∃ s, P s ∧ (S, s) ⟹ t


-- Syntactic Sugar
-- Allows writing [* P *] (S) [* Q *]
notation "[* " P " *] " "(" S ")" " [* " Q " *]"
  => IncorrectnessHoare P S Q

end Incorrectness
