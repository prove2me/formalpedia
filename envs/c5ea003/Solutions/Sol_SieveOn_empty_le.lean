-- Prove2me | solution 1 for SieveOn.empty_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:45:42.4176+00:00
-- url     : https://prove2.me/submissions/696b6713-8d52-4d5c-a2df-25197f8a5e87

import Mathlib
import Definitions.Def_Bridges_ToposTheoreticML_Foundations
open SieveOn in
theorem solution {α : Type*} [Preorder α] (d : α) (s : SieveOn α d) : SieveOn.empty d ≤ s := by
  intro x hx
  exact absurd hx (by simp [SieveOn.empty])
