-- Prove2me | solution 1 for lean_workbook_plus_54172
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:00:22.980441+00:00
-- url     : https://prove2.me/submissions/324a5ad6-d6cc-41a3-823b-9bcddd22a714

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ) :
  (x^2 + y^2 + z^2)^3 ≥ (x + y + z)^2 * (x^2 + y^2 + z^2 - x * y - x * z - y * z)^2 := by
  have hf : 0 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
  have h := mul_nonneg (sq_nonneg ((x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2)) hf
  nlinarith only [h]
