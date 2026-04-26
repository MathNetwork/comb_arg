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

-- One-command health check: build + axiom audit + LoC report.
-- Usage: `lake exe combarg-audit`
lean_exe «combarg-audit» where
  root := `Audit

-- Client-template generator: emits a starter min-max script
-- with `YourGMT.*` stubs.  Usage: `lake exe combarg-skeleton -N 5`
lean_exe «combarg-skeleton» where
  root := `Skeleton

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"