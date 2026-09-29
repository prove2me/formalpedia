-- Prove2me | solution 1 for lean_workbook_plus_22326
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:18.910836+00:00
-- url     : https://prove2.me/submissions/bc4834aa-a278-44b6-9935-a64462045457

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution {x y : ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : (x ^ 2 / a + y ^ 2 / b) * (a + b) ≥ (x + y) ^ 2 := by
  have hd : 0 < a*b := mul_pos ha hb
  have hi : (x^2/a+y^2/b)*(a+b)-(x+y)^2 = (b*x-a*y)^2/(a*b) := by
    field_simp
    ring
  have hn : 0 ≤ (b*x-a*y)^2/(a*b) := div_nonneg (sq_nonneg _) (le_of_lt hd)
  linarith
