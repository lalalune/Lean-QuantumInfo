import Lake
open System Lake DSL

package «quantumInfo»

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "a0aebd77a6619214a727994fade0e05203fc5252"

require "mathlib" from git "https://github.com/leanprover-community/mathlib4.git" @ "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

@[default_target]
lean_lib QuantumInfo

lean_lib ClassicalInfo

lean_lib StatMech

lean_lib Meta
lean_lib Thermodynamics
lean_lib Units
lean_lib Mathematics
lean_lib Mechanics
lean_lib ClassicalMechanics
lean_lib ClassicalFieldTheory
lean_lib Electromagnetism
lean_lib Optics
lean_lib QuantumMechanics
lean_lib Relativity
lean_lib SpaceAndTime where
  roots := #[`SpaceAndTime]
lean_lib Particles
lean_lib QFT
lean_lib QEC
lean_lib CondensedMatter
lean_lib Cosmology
lean_lib StringTheory
lean_lib Physics
lean_lib EUVLithography

lean_lib Test
