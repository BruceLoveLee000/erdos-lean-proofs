import Lake
open Lake DSL

package erdos_lean_proofs where

require formal_conjectures from git
  "https://github.com/google-deepmind/formal-conjectures" @ "c6f4b4bdab8fdabb19191a8a1648be21b81253b0"

@[default_target]
lean_lib ErdosProofs where
  globs := #[.submodules `ErdosProofs]
