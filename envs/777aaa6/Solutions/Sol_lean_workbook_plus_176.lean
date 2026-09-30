-- Prove2me | solution 1 for lean_workbook_plus_176
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:53.0244+00:00
-- url     : https://prove2.me/submissions/659e918a-8cda-40f7-a7ad-bae32815c61d

import Mathlib

theorem solution (s : ℝ) (hs : 9 / 4 ≤ s ∧ s ≤ 3) : 4 * s ^ 2 - 21 * s + 27 ≤ 0 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr hs.2)]
