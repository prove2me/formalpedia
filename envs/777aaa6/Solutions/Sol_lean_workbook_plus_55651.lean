-- Prove2me | solution 1 for lean_workbook_plus_55651
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:03:20.933777+00:00
-- url     : https://prove2.me/submissions/43482190-544e-453e-b4ac-93a882a90f95

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h1 : 0 < y ∧ y < x ∧ x ≤ 3) (h2 : x + y ≤ 5) : x^2 + y^2 ≤ 13 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
