-- Prove2me | solution 1 for lean_workbook_plus_8306
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:36.806409+00:00
-- url     : https://prove2.me/submissions/2954348d-aaca-468b-a55a-1aac8313bd4e

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hab : a + b + c = 3) (h : a = Real.sqrt (3 * x / (x + y + z))) (h' : b = Real.sqrt (3 * y / (x + y + z))) (h'' : c = Real.sqrt (3 * z / (x + y + z))) : a^2 + b^2 + c^2 = 3 → x^2 + y^2 + z^2 >= x * y + y * z + z * x := by
  intro _
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
