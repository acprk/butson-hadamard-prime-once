import Lake
open Lake DSL

package ButsonHadamardPrimeOnce where
  version := v!"0.1.0"
  description := "Group-invariant Butson Hadamard matrices: a prime dividing the order exactly once"
  license := "Apache-2.0"
  srcDir := "lean"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib OAI
