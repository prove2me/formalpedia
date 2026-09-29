-- Prove2me | solution 1 for sampleComplexityBound_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T05:52:30.237277+00:00
-- url     : https://prove2.me/submissions/6a9260ce-808f-4ec9-8bc9-37ce267652ab

import Mathlib
import Definitions.Def_Bridges_ToposTheoreticML_Foundations

theorem solution {d : ℕ} {ε δ : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < sampleComplexityBound d ε δ := by
  simp only [sampleComplexityBound]
  have h1 : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have h2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have h3 : 1 < 1 / δ := (one_lt_div hδ).mpr hδ1
  have h4 : 0 < Real.log (1 / δ) := Real.log_pos h3
  positivity
