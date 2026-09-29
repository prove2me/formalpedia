-- Prove2me | solution 1 for lean_workbook_plus_55444
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:53.45971+00:00
-- url     : https://prove2.me/submissions/19c36d22-d34f-4519-bf9a-1dd5389f6149

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {x y z : ℝ} (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x * y + x * z + y * z = 1) : x * (1 - y ^ 2 - z ^ 2 + y ^ 2 * z ^ 2) + y * (1 - z ^ 2 - x ^ 2 + z ^ 2 * x ^ 2) + z * (1 - x ^ 2 - y ^ 2 + x ^ 2 * y ^ 2) = 4 * x * y * z := by
  intros
  grind
