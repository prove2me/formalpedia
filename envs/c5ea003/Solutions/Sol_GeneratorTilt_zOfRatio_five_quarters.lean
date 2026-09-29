-- Prove2me | solution 1 for GeneratorTilt.zOfRatio_five_quarters
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:47:21.319036+00:00
-- url     : https://prove2.me/submissions/a0ca7303-5f1a-4097-854e-56e724d00a3e

import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio

open GeneratorTilt in
theorem solution :
    zOfRatio (5/4) =
      (2 * Real.sqrt 2 - Real.sqrt 5) / (Real.sqrt 5 * (Real.sqrt 2 - 1)) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have h2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2gt : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h54 : Real.sqrt (5 / 4) = Real.sqrt 5 / 2 := by
    rw [Real.sqrt_div (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  unfold zOfRatio
  rw [h54]
  have hne : Real.sqrt 2 - 1 ≠ 0 := by linarith
  have hne' : 1 - 1 / Real.sqrt 2 ≠ 0 := by
    have : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one h2]
      exact h2gt
    linarith
  field_simp
