-- Prove2me | solution 1 for CompressionOWF.K_le_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T09:42:07.090126+00:00
-- url     : https://prove2.me/submissions/a5f579a3-1207-47fb-a9a7-8b2664a29e0b

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
open CompressionOWF in
theorem solution {α : Type*} {D : Str → α} {p : Str} {y : α} (h : D p = y) : K D y ≤ p.length := by
  exact Nat.sInf_le ⟨p, rfl, h⟩
