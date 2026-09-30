-- Prove2me | solution 1 for lean_workbook_plus_38595
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:41:09.639884+00:00
-- url     : https://prove2.me/submissions/6c05016f-bb6e-49b6-a53f-6fd347628755

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ ∃ a : ℝ, a^6 + a^5 + 2*a^4 + 3*a^3 + 6*a^2 - a + 1 = 0 := by
  rintro ⟨a, ha⟩
  nlinarith [sq_nonneg (a^3 + a^2/2 + a), sq_nonneg (a^2 + 4*a/3), sq_nonneg (a - 3/22)]
