import Lake
open Lake DSL

package "lean_minicourse" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "reap" from git "https://github.com/frenzymath/reap.git" @ "feature/search"
require "leanprover-community" / "mathlib" @ "v4.24.0-rc1"

@[default_target]
lean_lib «Minicourse» where
  -- add any library configuration options here
