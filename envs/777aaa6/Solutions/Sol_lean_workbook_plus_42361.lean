-- Prove2me | solution 1 for lean_workbook_plus_42361
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:27:12.416194+00:00
-- url     : https://prove2.me/submissions/3496ca6d-7cda-414c-9f37-92eb2e42fd3c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a1 a2 b1 b2 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (hb1 : 0 < b1) (hb2 : 0 < b2) : (a1 ^ 2 / b1 + a2 ^ 2 / b2) ≥ (a1 + a2) ^ 2 / (b1 + b2) := by
  apply (div_le_iff₀ (add_pos hb1 hb2)).2
  field_simp
  nlinarith [sq_nonneg (a1*b2-a2*b1)]
