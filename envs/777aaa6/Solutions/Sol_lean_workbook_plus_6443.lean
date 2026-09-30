-- Prove2me | solution 1 for lean_workbook_plus_6443
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:11.802837+00:00
-- url     : https://prove2.me/submissions/139b6c94-d423-4e3d-9942-999493c158d9

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / (a * (b + 1)) + 1 / (b * (c + 1)) + 1 / (c * (a + 1))) ≥ 1 / (1 + a * b * c) := by
  have h1 : 0 < a * (b + 1) := by positivity
  have h2 : 0 < b * (c + 1) := by positivity
  have h3 : 0 < c * (a + 1) := by positivity
  have h4 : 0 < 1 + a * b * c := by positivity
  have hD : 0 < a * (b + 1) * (b * (c + 1)) * (c * (a + 1)) := by positivity
  -- the key identity: (1+abc)·N − 3·D is a sum of three nonnegative terms
  have key : (1 + a * b * c) * (b * (c + 1) * (c * (a + 1)) + a * (b + 1) * (c * (a + 1)) + a * (b + 1) * (b * (c + 1)))
      - 3 * (a * (b + 1) * (b * (c + 1)) * (c * (a + 1)))
      = b * c * (1 + c) * (1 - a * b) ^ 2 + c * a * (1 + a) * (1 - b * c) ^ 2 + a * b * (1 + b) * (1 - c * a) ^ 2 := by
    ring
  have t1 : 0 ≤ b * c * (1 + c) * (1 - a * b) ^ 2 := by positivity
  have t2 : 0 ≤ c * a * (1 + a) * (1 - b * c) ^ 2 := by positivity
  have t3 : 0 ≤ a * b * (1 + b) * (1 - c * a) ^ 2 := by positivity
  rw [ge_iff_le, div_add_div _ _ h1.ne' h2.ne', div_add_div _ _ (by positivity) h3.ne', div_le_div_iff₀ h4 (by positivity)]
  nlinarith [key, t1, t2, t3, hD]
