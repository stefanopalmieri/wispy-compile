import Lake
open Lake DSL

package «WispyScheme» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

@[default_target]
lean_lib «WispyScheme» where
  srcDir := "."
