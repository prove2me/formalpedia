-- Prove2me | solution 1 for lean_workbook_plus_66911
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:16:57.190076+00:00
-- url     : https://prove2.me/submissions/1a83ae95-383c-407f-a0ee-afc6a4336d1a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (habc : a * b * c = 1)
    (ha : a > 0) (hb : b > 0) (hc : c > 0) : a * b ^ 2 + a * c ^ 2 ≥ 1 := by
  nlinarith [mul_nonneg ha.le (sq_nonneg (b - c))]

#print axioms solution
