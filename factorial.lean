def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
