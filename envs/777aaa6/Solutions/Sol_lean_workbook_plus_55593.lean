-- Prove2me | solution 1 for lean_workbook_plus_55593
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:15:54.565178+00:00
-- url     : https://prove2.me/submissions/69994783-6e3d-401f-bcbc-2698492439a9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable def octic (x : ℝ) : ℝ := 2 * x ^ 8 + 3 * x ^ 2 + 6 - 5 * x ^ 3 - 4 * x

theorem unit_interval_certificate (x : ℝ) :
    octic x - 393216 / 390625 =
      2 * (x - 4 / 5) ^ 2 *
        (x ^ 6 + 2 * (4 / 5) * x ^ 5 + 3 * (4 / 5) ^ 2 * x ^ 4 +
          4 * (4 / 5) ^ 3 * x ^ 3 + 5 * (4 / 5) ^ 4 * x ^ 2 +
          6 * (4 / 5) ^ 5 * x + 7 * (4 / 5) ^ 6) +
      5 * x ^ 2 * (1 - x) + 2 * x * (1 - x) + (1033030 / 390625) * (1 - x) := by
  unfold octic
  ring

theorem unit_interval_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    393216 / 390625 ≤ octic x := by
  rw [← sub_nonneg, unit_interval_certificate]
  have hx : 0 ≤ 1 - x := by linarith
  positivity

theorem shifted_certificate (x : ℝ) :
    octic x - 2 = 2 * (x - 1) ^ 8 + 16 * (x - 1) ^ 7 + 56 * (x - 1) ^ 6 +
      112 * (x - 1) ^ 5 + 140 * (x - 1) ^ 4 + 107 * (x - 1) ^ 3 +
      44 * (x - 1) ^ 2 + 3 * (x - 1) := by unfold octic; ring

theorem large_input_bound (x : ℝ) (hx : 1 ≤ x) : 2 ≤ octic x := by
  rw [← sub_nonneg, shifted_certificate]
  have hp : 0 ≤ x - 1 := by linarith
  positivity

theorem nonpositive_input_bound (x : ℝ) (hx : x ≤ 0) : 6 ≤ octic x := by
  have hx3 : x ^ 3 ≤ 0 := by
    calc
      x ^ 3 = x ^ 2 * x := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hx
  have hx8 : 0 ≤ x ^ 8 := by positivity
  unfold octic
  nlinarith [sq_nonneg x]

theorem uniform_lower_bound (x : ℝ) : 393216 / 390625 ≤ octic x := by
  rcases le_total x 0 with hx | hx
  · have h := nonpositive_input_bound x hx
    linarith
  · rcases le_total x 1 with hx1 | hx1
    · exact unit_interval_bound x hx hx1
    · have h := large_input_bound x hx1
      linarith

theorem stronger_positivity (x : ℝ) : 1 < octic x := by
  have h := uniform_lower_bound x
  linarith

theorem solution (x : ℝ) : 2 * x ^ 8 + 3 * x ^ 2 + 6 - 5 * x ^ 3 - 4 * x > 0 := by
  have h := stronger_positivity x
  unfold octic at h
  linarith
