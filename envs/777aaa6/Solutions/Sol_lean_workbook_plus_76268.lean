-- Prove2me | solution 1 for lean_workbook_plus_76268
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:51.376818+00:00
-- url     : https://prove2.me/submissions/41104891-2a56-4b5a-895f-eb4547906f4b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℚ) (hx : x = 12 / 24) : x = 1 / 2 := by
  (intros; linarith)
