-- Prove2me | solution 1 for lean_workbook_plus_78918
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:21.065715+00:00
-- url     : https://prove2.me/submissions/f32c6703-7ece-4ba3-91fd-2c436f105eef

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) : (1 / (x + y) + 1 / (x + z)) ≥ 4 / (2 * x + y + z) := by
  apply (div_le_iff₀ (by linarith : 0<2*x+y+z)).2
  field_simp
  nlinarith [sq_nonneg (y-z)]
