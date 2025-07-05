import Lake
open Lake DSL

package «ledger-foundation» where
  -- add package configuration options here

lean_lib «foundation» {
  -- add library configuration options here
  srcDir := "foundation"
  -- Only include modules that compile cleanly for now
  globs := #[`Core.Phase1Working]
}

-- Original foundation library
lean_lib «EightFoundations» {
  globs := #[`EightFoundations]
}

-- We import mathlib for consistency, but our Core modules are designed to be self-contained
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
