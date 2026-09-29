-- Prove2me | solution 1 for lean_workbook_plus_48100
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:33.502811+00:00
-- url     : https://prove2.me/submissions/1d5afbb4-b177-49e0-9f9a-68fc4cf20707

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : √(8 + 4 * Real.sqrt 3) = √2 + √6 := by
  have hm : Real.sqrt 2 * Real.sqrt 6 = 2*Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num), show (2 : ℝ)*6=4*3 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have h3 := Real.sq_sqrt (show 0 ≤ (8 : ℝ)+4*Real.sqrt 3 by positivity)
  have hn : 0 ≤ Real.sqrt (8+4*Real.sqrt 3) := Real.sqrt_nonneg _
  have hr : 0 ≤ Real.sqrt 2+Real.sqrt 6 := by positivity
  nlinarith only [hm,h1,h2,h3,hn,hr]
