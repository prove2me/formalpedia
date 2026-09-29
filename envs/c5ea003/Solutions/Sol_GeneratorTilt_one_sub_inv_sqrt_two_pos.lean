-- Prove2me | solution 1 for GeneratorTilt.one_sub_inv_sqrt_two_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:27:54.272535+00:00
-- url     : https://prove2.me/submissions/7cbe2429-a623-4bb4-8e58-c5b617df2969

import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
theorem solution : 0 < 1 - 1 / Real.sqrt 2 := by
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using h
  have h2 : (0 : ℝ) < Real.sqrt 2 := by linarith
  have h3 : 1 / Real.sqrt 2 < 1 := by rw [div_lt_one h2]; exact h1
  linarith
