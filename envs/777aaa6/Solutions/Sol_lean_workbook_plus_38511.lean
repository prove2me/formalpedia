-- Prove2me | solution 1 for lean_workbook_plus_38511
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:03:03.948976+00:00
-- url     : https://prove2.me/submissions/dc5fec7f-7f8c-409a-88c8-3b165bd77deb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution (x y : ℝ) (m : ℤ) :
    (x ^ 3 * y ^ 3) ^ m = x ^ (3 * m) * y ^ (3 * m) := by
  rw [mul_zpow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  norm_num

#print axioms solution
