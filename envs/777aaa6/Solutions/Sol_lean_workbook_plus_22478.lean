-- Prove2me | solution 1 for lean_workbook_plus_22478
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:24.190755+00:00
-- url     : https://prove2.me/submissions/2e0b4f6b-6b06-4030-b8e8-c27a383afb8a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace AlternatingSexticPositive

noncomputable def value (x : ℝ) : ℝ := x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 3 / 4

theorem lower_bound (x : ℝ) : 1 / 4 ≤ value x := by
  by_cases hx0 : x ≤ 0
  · have hx3 : x ^ 3 ≤ 0 := by
      simpa only [pow_succ] using mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hx0
    have hx5 : x ^ 5 ≤ 0 := by
      simpa only [pow_succ] using mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ x ^ 4 by positivity) hx0
    have hx4 : 0 ≤ x ^ 4 := by positivity
    have hx6 : 0 ≤ x ^ 6 := by positivity
    dsimp [value]
    nlinarith [sq_nonneg x]
  have hxpos : 0 < x := lt_of_not_ge hx0
  by_cases hx1 : x ≤ 1
  · have hid : (x + 1) * (value x - 1 / 4) = x ^ 7 + (1 - x) / 2 := by
      unfold value
      ring
    by_contra h
    have hneg : (x + 1) * (value x - 1 / 4) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    rw [hid] at hneg
    nlinarith [pow_nonneg hxpos.le 7]
  · have hx1pos : 0 ≤ x - 1 := by linarith
    have h5 := mul_nonneg (pow_nonneg hxpos.le 5) hx1pos
    have h3 := mul_nonneg (pow_nonneg hxpos.le 3) hx1pos
    have h1 := mul_nonneg hxpos.le hx1pos
    dsimp [value]
    nlinarith only [h5, h3, h1]

end AlternatingSexticPositive

theorem solution : ¬ ∃ x : ℝ,
    x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 3 / 4 = 0 := by
  rintro ⟨x, hx⟩
  have h := AlternatingSexticPositive.lower_bound x
  dsimp [AlternatingSexticPositive.value] at h
  linarith

#print axioms AlternatingSexticPositive.lower_bound
#print axioms solution
