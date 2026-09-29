-- Prove2me | solution 1 for lean_workbook_plus_59138
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:33.003781+00:00
-- url     : https://prove2.me/submissions/e5fd8917-bcbc-49e8-a87c-273e46cfc414

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} (h : a + b + c = 0) :
  (a^5 + b^5 + c^5) / 5 = (a^2 + b^2 + c^2) / 2 * (a^3 + b^3 + c^3) / 3 := by
  have hc : c = -a-b := by linarith
  rw [hc]
  ring
