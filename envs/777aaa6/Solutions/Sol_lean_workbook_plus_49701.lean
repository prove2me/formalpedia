-- Prove2me | solution 1 for lean_workbook_plus_49701
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:35:51.215651+00:00
-- url     : https://prove2.me/submissions/5e589f2d-dabd-4957-8f13-651fc611fb7a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ((2 : ℝ) / 3 * 1 / 2) / (2 / 3 * 1 / 2 + 1 / 3 * 2 / 3) = 3 / 5 := by
  norm_num
