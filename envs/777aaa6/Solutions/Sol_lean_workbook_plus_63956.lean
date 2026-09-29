-- Prove2me | solution 1 for lean_workbook_plus_63956
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:37.702517+00:00
-- url     : https://prove2.me/submissions/83fd2f68-0a03-4e7a-9c56-2c9d665534c3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {x y : ℝ} : (x - y) ^ 2 * (2 * x + y) ^ 2 * (x + 2 * y) ^ 2 ≥ 0 := by
  (intros; positivity)
