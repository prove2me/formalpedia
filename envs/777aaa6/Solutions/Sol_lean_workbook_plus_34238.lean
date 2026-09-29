-- Prove2me | solution 1 for lean_workbook_plus_34238
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:27.292264+00:00
-- url     : https://prove2.me/submissions/aef8ebd0-6a7b-45bc-8a63-a5dc711155cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ (1 / 3) * (x + y + z) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
