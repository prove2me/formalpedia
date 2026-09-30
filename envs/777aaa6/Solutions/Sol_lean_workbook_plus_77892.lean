-- Prove2me | solution 1 for lean_workbook_plus_77892
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:34.808906+00:00
-- url     : https://prove2.me/submissions/eae94043-6c13-4487-bc88-ed876ccf8e81

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c x y z : ℝ) (ha : a = x * (y - z) ^ 2)
    (hb : b = y * (z - x) ^ 2) (hc : c = z * (x - y) ^ 2) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ 2 * (a * b + b * c + c * a) := by
  have hid : a ^ 2 + b ^ 2 + c ^ 2 - 2 * (a * b + b * c + c * a) =
      ((x - y) * (y - z) * (z - x)) ^ 2 := by
    rw [ha, hb, hc]
    ring
  nlinarith [sq_nonneg ((x - y) * (y - z) * (z - x))]

#print axioms solution
