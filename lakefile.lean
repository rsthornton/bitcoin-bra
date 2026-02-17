import Lake
open Lake DSL

package «bitcoin-bra» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩  -- Force explicit universe/variable declarations
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «BRA» where
  srcDir := "."
  roots := #[`BRA]

lean_lib «Bitcoin» where
  srcDir := "."
  roots := #[`Bitcoin]

lean_lib «Comparison» where
  srcDir := "."
  roots := #[`Comparison]
