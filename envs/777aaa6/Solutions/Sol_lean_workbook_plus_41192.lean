-- Prove2me | solution 1 for lean_workbook_plus_41192
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:43.999015+00:00
-- url     : https://prove2.me/submissions/759275c1-d5d0-4ad9-b127-94bf9538fb3f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 ≥ x * y * z * (x + y + z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
