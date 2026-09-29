-- Prove2me | solution 1 for GeneratorTilt.scan_order_scope_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:20:48.480135+00:00
-- url     : https://prove2.me/submissions/1456bd91-a445-4bde-b754-fb142c6fcfdc

import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
open GeneratorTilt in
theorem solution {r : ℝ} (hr : 0 < r) :
    (r < criticalRatio → 1 / 2 < zOfRatio r) ∧
    (criticalRatio < r → zOfRatio r < 1 / 2) := by
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
  rw [criticalRatio] at *
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hzeq, lt_div_iff₀ hden]
    nlinarith [hu, ha, ha2, hu2, h]
  · rw [hzeq, div_lt_iff₀ hden]
    nlinarith [hu, ha, ha2, hu2, h]
