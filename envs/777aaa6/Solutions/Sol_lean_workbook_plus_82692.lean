-- Prove2me | solution 1 for lean_workbook_plus_82692
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:31:10.95631+00:00
-- url     : https://prove2.me/submissions/68c0a003-718b-4eab-ac6e-5e41c8bd9c77

import Mathlib

theorem solution (a : ℝ) (ha : 0 < a) : (a^4 + 9)/(10*a) > 4/5 := by
  apply (lt_div_iff₀ (by positivity : 0 < 10*a)).2
  nlinarith only [sq_nonneg (a^2-2), sq_nonneg (a-1)]
