import Lake
open Lake DSL

package Maths where
  -- Additional project-level settings can go here

lean_lib Maths where
  -- Default library configuration (sources live under Maths/ by convention)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master" 