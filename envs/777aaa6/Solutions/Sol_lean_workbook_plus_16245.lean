-- Prove2me | solution 1 for lean_workbook_plus_16245
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:03.08053+00:00
-- url     : https://prove2.me/submissions/81581f50-ef5d-409a-bc03-feef78cc786a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
