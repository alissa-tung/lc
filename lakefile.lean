import Lake
open Lake DSL

package «lc» where

@[default_target]
lean_lib «Lc» where

lean_exe «lc» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
