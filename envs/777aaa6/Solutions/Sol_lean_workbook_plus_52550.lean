-- Prove2me | solution 1 for lean_workbook_plus_52550
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:50.611347+00:00
-- url     : https://prove2.me/submissions/246e6946-3b15-411a-8140-f799195a5c28

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℚ) : x = 25 / 4 + 49 / 12 → 60 * x = 620 := by
  (intros; linarith)
