-- Prove2me | solution 1 for lean_workbook_plus_28511
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:39.119789+00:00
-- url     : https://prove2.me/submissions/a0260cef-b8b4-451b-be03-24c11267495c

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℂ) (h : x + y + z = 0) : x^7 + y^7 + z^7 = 7 * x * y * z * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) := by
  have hz : z = -x - y := by linear_combination h
  subst hz
  ring
