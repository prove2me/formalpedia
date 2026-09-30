-- Prove2me | solution 1 for lean_workbook_plus_14861
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:41:02.183267+00:00
-- url     : https://prove2.me/submissions/7c1cfb21-e53f-4af8-92ca-ba31fe86926d

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b) ≤ (a + b) * (a + c) * (b + d) * (c + d) := by
  have key : (a + b) * (a + c) * (b + d) * (c + d) - (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b) = (a * d - b * c) ^ 2 := by ring
  nlinarith [sq_nonneg (a * d - b * c)]
