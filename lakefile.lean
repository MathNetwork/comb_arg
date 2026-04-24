import Lake
open Lake DSL

package «comb-arg» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «CombArg» where

lean_lib «test» where
  globs := #[.submodules `test]

lean_lib «examples» where
  globs := #[.submodules `examples]
