import Lake
open Lake DSL

package "swim_mathlib" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

require swim from ".."

@[default_target]
lean_lib «SwimMathlibProofs»
