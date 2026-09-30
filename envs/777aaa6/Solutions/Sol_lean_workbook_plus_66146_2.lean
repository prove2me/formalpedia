-- Prove2me | solution 2 for lean_workbook_plus_66146
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:21.346484+00:00
-- url     : https://prove2.me/submissions/60226556-05b2-439f-be00-dcffcc1824e9

import Mathlib

theorem solution (a : ℝ) (ha1 : 1 ≥ a) (ha2 : a ≥ 1 / 3) :
    4 * a ^ 3 + 2 * a ^ 2 + 13 * a - 1 ≥ 0 := by
  have ha : 0 ≤ a := by linarith
  nlinarith [pow_nonneg ha 3, sq_nonneg a]
