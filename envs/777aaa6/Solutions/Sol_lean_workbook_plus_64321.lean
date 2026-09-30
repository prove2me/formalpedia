-- Prove2me | solution 1 for lean_workbook_plus_64321
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:36:49.02635+00:00
-- url     : https://prove2.me/submissions/0ee32be3-b7d5-4127-b164-9bb1c3e6a762

import Mathlib

theorem solution (x y : ℝ) (hx : abs (x+y) + abs (x-y) = 2) :
    3/2 ≤ abs (2*x-y) + abs (2*y-x) ∧ abs (2*x-y) + abs (2*y-x) ≤ 6 := by
  have hs : |x+y| ≤ |2*x-y| + |2*y-x| := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (2*x-y), neg_le_abs (2*x-y),
      le_abs_self (2*y-x), neg_le_abs (2*y-x)]
  have ht : |x-y| ≤ (|2*x-y| + |2*y-x|)/3 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (2*x-y), neg_le_abs (2*x-y),
      le_abs_self (2*y-x), neg_le_abs (2*y-x)]
  have hu : |2*x-y| ≤ (|x+y| + 3*|x-y|)/2 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (x+y), neg_le_abs (x+y),
      le_abs_self (x-y), neg_le_abs (x-y)]
  have hv : |2*y-x| ≤ (|x+y| + 3*|x-y|)/2 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (x+y), neg_le_abs (x+y),
      le_abs_self (x-y), neg_le_abs (x-y)]
  constructor
  · linarith only [hx, hs, ht]
  · linarith only [hx, hu, hv, abs_nonneg (x+y)]

theorem bounds_attained :
    (∃ x y : ℝ, |x+y| + |x-y| = 2 ∧ |2*x-y| + |2*y-x| = 3/2) ∧
    (∃ x y : ℝ, |x+y| + |x-y| = 2 ∧ |2*x-y| + |2*y-x| = 6) := by
  constructor
  · exact ⟨1, 1/2, by norm_num <;> ring, by norm_num <;> ring⟩
  · exact ⟨1, -1, by simp <;> norm_num, by norm_num⟩
