-- Prove2me | solution 1 for lean_workbook_plus_68079
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:51:41.675405+00:00
-- url     : https://prove2.me/submissions/7945fb54-46ae-45d1-b065-b9a139d1be80

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QuarticDifferenceBound

def expression (x y : ℝ) : ℝ :=
  8 * (x ^ 2 - x * y + y ^ 2) ^ 2 -
    (x ^ 2 + y ^ 2) * (x ^ 2 + 2 * x * y + y ^ 2)

theorem decomposition (x y : ℝ) :
    expression x y =
      9 / 2 * ((x - y) ^ 2) ^ 2 + 5 / 2 * (x ^ 2 - y ^ 2) ^ 2 := by
  unfold expression
  ring

theorem nonnegative (x y : ℝ) : 0 ≤ expression x y := by
  rw [decomposition]
  nlinarith [sq_nonneg ((x - y) ^ 2), sq_nonneg (x ^ 2 - y ^ 2)]

theorem equality_iff (x y : ℝ) : expression x y = 0 ↔ x = y := by
  constructor
  · intro h
    rw [decomposition] at h
    have hfourth : ((x - y) ^ 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((x - y) ^ 2), sq_nonneg (x ^ 2 - y ^ 2)]
    have hdiff : x - y = 0 := eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero hfourth)
    exact sub_eq_zero.mp hdiff
  · rintro rfl
    unfold expression
    ring

theorem strict_iff (x y : ℝ) : 0 < expression x y ↔ x ≠ y := by
  constructor
  · intro h hxy
    have hz := (equality_iff x y).2 hxy
    linarith
  · intro hxy
    have hne : expression x y ≠ 0 := fun h => hxy ((equality_iff x y).1 h)
    exact lt_of_le_of_ne (nonnegative x y) hne.symm

theorem equality_on_domain (x y : ℝ) (h : 0 < x + y) :
    expression x y = 0 ↔ x = y ∧ 0 < x := by
  rw [equality_iff]
  constructor
  · intro hxy
    exact ⟨hxy, by linarith⟩
  · exact And.left

end QuarticDifferenceBound

theorem solution (x y : ℝ) (h : x + y > 0) :
    8 * (x ^ 2 - x * y + y ^ 2) ^ 2 -
      (x ^ 2 + y ^ 2) * (x ^ 2 + 2 * x * y + y ^ 2) ≥ 0 := by
  exact QuarticDifferenceBound.nonnegative x y
