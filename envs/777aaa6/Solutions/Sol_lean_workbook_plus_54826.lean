-- Prove2me | solution 1 for lean_workbook_plus_54826
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:46.598256+00:00
-- url     : https://prove2.me/submissions/fc2faf99-50de-453b-a4b4-1f3046fc1e37

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h : a + b + c + d = 0) : d = -a - b - c := by
  (intros; linarith)
