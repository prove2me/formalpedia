-- Prove2me | solution 1 for lean_workbook_plus_46862
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:14:33.284044+00:00
-- url     : https://prove2.me/submissions/3f2dd71f-ac66-4f34-ba1c-6b6d7a168e89

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + x * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
