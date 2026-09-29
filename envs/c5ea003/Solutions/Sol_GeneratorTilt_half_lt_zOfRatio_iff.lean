-- Prove2me | solution 1 for GeneratorTilt.half_lt_zOfRatio_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:23:52.834983+00:00
-- url     : https://prove2.me/submissions/939e976c-4e15-44d6-99f8-b13c8f301e90

import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
open GeneratorTilt in
theorem solution {r : ℝ} (hr : 0 < r) : 1 / 2 < zOfRatio r ↔ r < criticalRatio := by
  have ha : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha1 : 1 < Real.sqrt 2 := by nlinarith [ha, ha2]
  have hu : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hu2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hden : 0 < Real.sqrt r * (Real.sqrt 2 - 1) := by
    have : (0:ℝ) < Real.sqrt 2 - 1 := by linarith
    positivity
  have hzeq : zOfRatio r
      = (Real.sqrt 2 - Real.sqrt r) / (Real.sqrt r * (Real.sqrt 2 - 1)) := by
    unfold zOfRatio
    have h1 : Real.sqrt 2 ≠ 0 := ne_of_gt ha
    have h2 : Real.sqrt r ≠ 0 := ne_of_gt hu
    have h3 : Real.sqrt 2 - 1 ≠ 0 := by intro hh; nlinarith
    field_simp
  rw [hzeq, criticalRatio, lt_div_iff₀ hden]
  constructor
  · intro h
    nlinarith [hu, ha, ha2, hu2, h]
  · intro h
    nlinarith [hu, ha, ha2, hu2, h]
