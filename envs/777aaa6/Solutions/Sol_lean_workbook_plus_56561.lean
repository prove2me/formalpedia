-- Prove2me | solution 1 for lean_workbook_plus_56561
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:17:56.167813+00:00
-- url     : https://prove2.me/submissions/085db57b-059e-48fb-ba25-3bd852bcdbbf

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (hab : a + b + c = 0) : (a^5 + b^5 + c^5) / 5 = (a^3 + b^3 + c^3) / 3 * (a^2 + b^2 + c^2) / 2 := by
  have hc : c = -a - b := by linarith
  subst hc
  ring
