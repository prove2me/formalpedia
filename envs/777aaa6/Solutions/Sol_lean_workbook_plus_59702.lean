-- Prove2me | solution 1 for lean_workbook_plus_59702
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:58.973583+00:00
-- url     : https://prove2.me/submissions/f8c5ef0e-0f26-4bb4-8e38-bd88be4b8bc2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

private theorem reciprocal_tangent (x r : ℝ) (hx : 0 < x) (hr : 0 ≤ r)
    (hr2 : r ^ 2 = 3) : 5 * r / 3 ≤ x + 1 / x + r * x ^ 2 := by
  have hid : x + 1 / x + r * x ^ 2 - 5 * r / 3 =
      (r * x - 1) ^ 2 * (r * x + 3) / (3 * x) := by
    field_simp
    linear_combination -(x ^ 2 * (r * x + 1)) * hr2
  have hpos : 0 ≤ (r * x - 1) ^ 2 * (r * x + 3) / (3 * x) := by positivity
  linarith [hid]

private theorem normalized_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    1 / a + 1 / b + 1 / c + a + b + c ≥ 4 * Real.sqrt 3 := by
  have hr : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h1 := reciprocal_tangent a (Real.sqrt 3) ha hr hr2
  have h2 := reciprocal_tangent b (Real.sqrt 3) hb hr hr2
  have h3 := reciprocal_tangent c (Real.sqrt 3) hc hr hr2
  have heq : Real.sqrt 3 * (a ^ 2 + b ^ 2 + c ^ 2) = Real.sqrt 3 := by rw [h]; ring
  nlinarith only [h1, h2, h3, heq]

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    1 / a + 1 / b + 1 / c + a + b + c ≥ 4 * Real.sqrt 3 := by
  exact normalized_bound a b c ha hb hc h
