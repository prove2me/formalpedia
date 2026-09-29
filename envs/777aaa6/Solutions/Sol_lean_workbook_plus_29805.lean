-- Prove2me | solution 1 for lean_workbook_plus_29805
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:42.443623+00:00
-- url     : https://prove2.me/submissions/2146f8e8-1873-4bc0-9d54-00365acb0fb8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℤ) : x = y → x * (x - 1) = y * (y - 1) := by
  (intros; simp_all)
