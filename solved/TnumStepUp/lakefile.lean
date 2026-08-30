import Lake
open Lake DSL

package «ebpf-tnumstepup» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

@[default_target]
lean_lib «VeroTask» where
  roots := #[`Task]
