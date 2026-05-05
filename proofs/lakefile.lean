import Lake
open Lake DSL

package "CategoricalInterventionsProofs" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib «CategoricalInterventionsProofs» where
  globs := #[.submodules `CategoricalInterventionsProofs]
