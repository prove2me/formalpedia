-- Prove2me | solution 1 for CompressionOWF.exists_shortest
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:20:27.463972+00:00
-- url     : https://prove2.me/submissions/12b2808e-7072-4900-b959-7768208ff774

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
open CompressionOWF in
theorem solution {α : Type*} {D : Str → α} {y : α} (h : Describable D y) :
    ∃ p : Str, p.length = K D y ∧ D p = y := by
  obtain ⟨p₀, hp₀⟩ := h
  exact Nat.sInf_mem (s := {n | ∃ p : Str, p.length = n ∧ D p = y}) ⟨p₀.length, p₀, rfl, hp₀⟩
