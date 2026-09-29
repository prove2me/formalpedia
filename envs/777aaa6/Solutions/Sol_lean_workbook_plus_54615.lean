-- Prove2me | solution 1 for lean_workbook_plus_54615
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:24.512706+00:00
-- url     : https://prove2.me/submissions/49f8b85c-4b9a-41b0-99d6-f90bb04913d6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x ^ 3 + y ^ 3) * (x + y) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
