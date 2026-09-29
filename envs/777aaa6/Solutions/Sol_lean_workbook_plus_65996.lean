-- Prove2me | solution 1 for lean_workbook_plus_65996
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:48.114909+00:00
-- url     : https://prove2.me/submissions/47514bc0-c128-4b82-9880-592c3b3a82af

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a c : ℝ) : (a^2 + c^2)^2 ≤ 2 * (a^4 + c^4) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (c), sq_nonneg (a - c), sq_nonneg (a + c)])
