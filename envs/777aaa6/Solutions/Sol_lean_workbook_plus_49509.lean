-- Prove2me | solution 1 for lean_workbook_plus_49509
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:27.160693+00:00
-- url     : https://prove2.me/submissions/051b4a91-241f-4658-83a9-68e2f2e0e4c7

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : 4*a*b ≤ 2 + a^2*b^2*(a^2 + b^2 + 2 - 2*a*b) := by
  nlinarith [sq_nonneg (a*b*(a-b)),sq_nonneg (a*b-1)]
