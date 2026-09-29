-- Prove2me | solution 2 for MultiverseModalForcing.B_fails
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T06:26:03.77031+00:00
-- url     : https://prove2.me/submissions/81e69210-47f7-4634-8bfa-7bd9ae644b95

import Mathlib
import Definitions.Def_Applications_ProofTheoryAndLogic_MultiverseModalForcing
open MultiverseModalForcing in
theorem solution :
    ¬ MValid sinkFrame.R sinkFrame.M
        (.imp (.atom true) (.box (MSentence.dia (.atom true)))) := by
  intro h
  -- at `wT` the atom holds, so `□◇ atom` would have to hold there
  have h1 := h wT (Set.mem_univ _)
  simp only [sinkFrame, meval, MSentence.dia] at h1
  -- but `wT` can force to the sink `wF`, where the atom is false forever
  have h2 := h1 rfl wF (Or.inl rfl) (Set.mem_univ _)
  apply h2
  intro u hu _
  rcases hu with rfl | rfl <;> simp [wF]
