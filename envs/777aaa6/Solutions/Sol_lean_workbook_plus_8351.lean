-- Prove2me | solution 1 for lean_workbook_plus_8351
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:43.372997+00:00
-- url     : https://prove2.me/submissions/b1851b2f-6d29-4387-ace1-a1fde1489898

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y α β : ℝ) : (x * β - y * α) ^ 2 ≥ 0 := by
  (intros; positivity)
