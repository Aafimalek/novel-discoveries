import Lake
open Lake DSL

package «es33» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"

@[default_target]
lean_lib ES33
