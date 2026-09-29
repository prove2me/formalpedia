-- Prove2me | solution 1 for lean_workbook_plus_15286
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:05.351838+00:00
-- url     : https://prove2.me/submissions/be464cf8-61d8-4104-849b-a7f24d13145d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≠ 0) : x * y = x * z → y = z := by
  (intros; simp_all)
