import Lake
open Lake DSL

package «switch13_forum» where

lean_lib Switch13Core where
  roots := #[`Switch13Core]

lean_lib Switch13Reachability where
  roots := #[`Switch13Reachability]

lean_lib Switch13Package where
  roots := #[`Switch13Package]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"
