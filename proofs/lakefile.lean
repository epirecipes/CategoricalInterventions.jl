import Lake
open Lake DSL

package "CategoricalInterventionsProofs" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

@[default_target]
lean_lib «CategoricalInterventionsProofs» where
  globs := #[.submodules `CategoricalInterventionsProofs,
    -- the SA-Pass audit (shadows, checkers, `sa_check_*` commands); see design/SA-PASS.md
    .andSubmodules `CategoricalInterventionsProofs.SAPass]
