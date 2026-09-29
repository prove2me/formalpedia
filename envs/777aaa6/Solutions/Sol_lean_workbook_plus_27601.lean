-- Prove2me | solution 1 for lean_workbook_plus_27601
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:11.636299+00:00
-- url     : https://prove2.me/submissions/c14abe37-9783-4ba3-8056-5f9067bd786a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : (x - y) ^ 2 + (y - z) ^ 2 + (x - z) ^ 2 ≥ 0 := by
  (intros; positivity)
