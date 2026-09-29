-- Prove2me | solution 1 for lean_workbook_plus_49098
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:04.106298+00:00
-- url     : https://prove2.me/submissions/03de990b-b064-427c-8140-913390a96525

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x ≠ 0) : x * y = x → y = 1 := by
  (intros; simp_all)
