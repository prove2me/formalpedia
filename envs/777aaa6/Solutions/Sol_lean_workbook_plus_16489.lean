-- Prove2me | solution 1 for lean_workbook_plus_16489
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:36.90759+00:00
-- url     : https://prove2.me/submissions/0b2d5336-cb05-411f-94d6-321c8830d26b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a : ℝ) : a - a ^ 3 / 2 + 2 * a ≤ 2 * Real.sqrt 2 ↔ (a - Real.sqrt 2) ^ 2 * (a + 2 * Real.sqrt 2) ≥ 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hi : (a - Real.sqrt 2)^2 * (a + 2 * Real.sqrt 2) = a^3 - 6*a + 4*Real.sqrt 2 := by
    nlinarith [congrArg (fun t : ℝ => a * t) hs, congrArg (fun t : ℝ => Real.sqrt 2 * t) hs]
  constructor <;> intro h <;> linarith
