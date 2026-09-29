-- Prove2me | solution 1 for lean_workbook_plus_79782
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:23.935931+00:00
-- url     : https://prove2.me/submissions/9777c05d-6627-4471-9f99-3581ab3159c0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℚ) (hx : x = 9 / 15) : x = 0.6 := by
  (intros; linarith)
