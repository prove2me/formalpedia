-- Prove2me | solution 1 for lean_workbook_plus_7837
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:55.790055+00:00
-- url     : https://prove2.me/submissions/841d1a58-973d-47f3-8a45-a85d38a27f56

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℚ) (hx : x = 59 / 12 / 17) : x = 59 / 204 := by
  (intros; linarith)
