-- Prove2me | solution 1 for lean_workbook_plus_31473
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:42.371699+00:00
-- url     : https://prove2.me/submissions/0a7d11ff-9dec-4a1d-b734-56203c2664fd

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p₁ : ℝ)
  (h₀ : p₁ = 1 / 16 + 15 / 32 * p₁) :
  p₁ = 2 / 17 := by
  linarith
