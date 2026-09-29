-- Prove2me | solution 1 for lean_workbook_plus_51867
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:00:26.17505+00:00
-- url     : https://prove2.me/submissions/e3e1ad17-d4be-4dc0-8647-b64aaf959e49

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : √2 + √3 = √(2 + 3 + 2 * Real.sqrt 6) := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hm : Real.sqrt 2*Real.sqrt 3=Real.sqrt 6 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  apply Eq.symm
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  nlinarith only [h2,h3,hm]
