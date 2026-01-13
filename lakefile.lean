import Lake
open Lake DSL

package «projem» where
  -- Paket ayarları

@[default_target]
lean_lib «Projem» where
  srcDir := "."
  roots := #[`Language, `Hoare_Defs]
