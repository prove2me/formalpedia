-- Prove2me | solution 1 for lean_workbook_plus_32605
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:42:11.496873+00:00
-- url     : https://prove2.me/submissions/da99709b-b3cd-41b6-ad3d-49daab9253dc

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : x^6 - x^5 + x^4 - x^3 + x^2 - x + 2/5 > 0 := by
  -- x^6 - x^5 + x^4 - x^3 + x^2 - x + 2/5
  --   = (x^2 * (x - 1/2))^2 + (3/4) * (x * (x - 2/3))^2 + (2/3) * (x - 3/4)^2 + 1/40
  nlinarith [sq_nonneg (x^2 * (x - 1/2)), sq_nonneg (x * (x - 2/3)), sq_nonneg (x - 3/4)]
