-- Prove2me | solution 1 for lean_workbook_plus_82102
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:08:50.34832+00:00
-- url     : https://prove2.me/submissions/224cb564-85c5-49f3-834f-fc308cc5c510

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (x y z : ℝ) (_hx : 0 < x) (_hy : 0 < y) (_hz : 0 < z)
    (h : x + y + z = 4) :
    (x * y + y * z + z * x) ≤ 16 / 3 ∧
      (∃ x y z : ℝ, (x * y + y * z + z * x) = 16 / 3) := by
  constructor
  · nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  · refine ⟨4 / 3, 4 / 3, 4 / 3, ?_⟩
    norm_num

#print axioms solution
