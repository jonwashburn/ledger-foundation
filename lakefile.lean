import Lake
open Lake DSL

package «ledger-foundation» where
  -- add package configuration options here

lean_lib «foundation» {
  -- add library configuration options here
  srcDir := "foundation"
  globs := #[`Core.SelfContainedDerivation, `Core.RecognitionLength, `Core.FundamentalTick,
            `Core.MassEnergyCascade, `Core.CompleteDerivation,
            `Core.NumericalVerification, `Core.CosmologicalDerivation, `Core.GaugeTheoryConnection,
            `Core.QuantumFieldTheory, `Core.UnifiedFramework, `Core.ExperimentalPredictions]
}

-- Original foundation library
lean_lib «EightFoundations» {
  globs := #[`EightFoundations]
}

-- We import mathlib for consistency, but our Core modules are designed to be self-contained
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
