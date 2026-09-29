-- Prove2me | solution 1 for lean_workbook_plus_52296
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:07.645431+00:00
-- url     : https://prove2.me/submissions/2fe09280-2045-4909-ad6d-4d9d9e5feae8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x : ℝ) : x / (x^2 + 1) ≤ 1 / 2 := by
  apply (div_le_iff₀ (by positivity : 0 < x^2+1)).2
  nlinarith [sq_nonneg (x-1)]
