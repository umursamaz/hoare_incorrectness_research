import Lake
open Lake DSL

package hoare_incorrectness

lean_lib Language where
  roots := #[`Language]

lean_lib AExp where
  roots := #[`AExp]

lean_lib PExp where
  roots := #[`PExp]

lean_lib Hoare
lean_lib Incorrectness
