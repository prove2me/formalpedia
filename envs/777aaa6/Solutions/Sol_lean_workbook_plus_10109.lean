-- Prove2me | solution 1 for lean_workbook_plus_10109
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:39.163359+00:00
-- url     : https://prove2.me/submissions/239ebaf6-d490-4f83-b087-2a4c298bd5f9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b^2 = 1) : a * b + 2 * a + 3 * b ≤ 94 / 27 := by
  have hp : 0≤(b-2/3)^2*(b+10/3) := mul_nonneg (sq_nonneg _) (by linarith)
  have hm := congrArg (fun t : ℝ => t*b) hab
  nlinarith only [hp, hab, hm]
