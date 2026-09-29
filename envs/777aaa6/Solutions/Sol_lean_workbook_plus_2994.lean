-- Prove2me | solution 1 for lean_workbook_plus_2994
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:12.404957+00:00
-- url     : https://prove2.me/submissions/c291db43-7a06-4174-b92c-a62854459d4b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x - y) ^ 2 + (x - 1) ^ 2 + (y - 1) ^ 2 ≥ 0 := by
  (intros; positivity)
