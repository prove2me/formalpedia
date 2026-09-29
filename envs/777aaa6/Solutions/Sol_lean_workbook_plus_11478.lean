-- Prove2me | solution 1 for lean_workbook_plus_11478
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:49.815479+00:00
-- url     : https://prove2.me/submissions/882a95ba-ad36-4414-a5c8-7e52efa66afe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℚ) (hx : x = 70) : ⌈x⌉ = 70 := by
  (intros; simp_all)
