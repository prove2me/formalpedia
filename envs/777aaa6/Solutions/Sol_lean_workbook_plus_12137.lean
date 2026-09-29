-- Prove2me | solution 1 for lean_workbook_plus_12137
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:33.64444+00:00
-- url     : https://prove2.me/submissions/1f7d8ae3-0674-4cb2-af1f-94fc1481d68a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (abs x * y ^ 2 - x ^ 2 * abs y) ^ 2 + (2 * abs (x * y) + 1) * (abs (x * y) - 1) ^ 2 ≥ 0 := by
  (intros; positivity)
