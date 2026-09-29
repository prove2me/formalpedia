-- Prove2me | solution 1 for lean_workbook_plus_30901
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:27.861983+00:00
-- url     : https://prove2.me/submissions/06fa6dd7-f107-49b8-901a-da399755e0db

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c k : ℝ) : k + 2 = 2 * (a + b + c) / a → 2 / (k + 2) = a / (a + b + c) := by
  intro h
  rw [h]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring
