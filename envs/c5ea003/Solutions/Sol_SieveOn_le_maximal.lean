-- Prove2me | solution 1 for SieveOn.le_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:50:15.095448+00:00
-- url     : https://prove2.me/submissions/17dcd7a3-acf7-4c7e-9407-fbbd3e470cb3

import Mathlib
import Definitions.Def_Bridges_ToposTheoreticML_Foundations
open SieveOn in
theorem solution {α : Type*} [Preorder α] (d : α) (s : SieveOn α d) : s ≤ SieveOn.maximal d := by
  intro x hx
  exact s.below_target x hx
