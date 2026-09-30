-- Prove2me | solution 1 for lean_workbook_plus_16247
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:23:06.004393+00:00
-- url     : https://prove2.me/submissions/d98a176a-af52-4bbb-8c7b-4e953ee29470

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : (x + 1) * (x ^ 2 + 1) * (x ^ 3 + 1) ≤ 4 * (x ^ 6 + 1) := by
  -- (x+1)(x^3+1) ≤ 2(x^4+1) since 2(x^4+1) - (x+1)(x^3+1) = (x-1)^2 (x^2+x+1) ≥ 0,
  -- (x^2+1)(x^4+1) ≤ 2(x^6+1) since the difference is (x^2-1)^2 (x^2+1) ≥ 0.
  have h1 : (x + 1) * (x ^ 3 + 1) ≤ 2 * (x ^ 4 + 1) := by
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) (by nlinarith [sq_nonneg (x + 1/2)] : (0:ℝ) ≤ x ^ 2 + x + 1)]
  have h2 : (x ^ 2 + 1) * (x ^ 4 + 1) ≤ 2 * (x ^ 6 + 1) := by
    nlinarith [mul_nonneg (sq_nonneg (x ^ 2 - 1)) (by positivity : (0:ℝ) ≤ x ^ 2 + 1)]
  have h3 : 0 ≤ x ^ 2 + 1 := by positivity
  calc (x + 1) * (x ^ 2 + 1) * (x ^ 3 + 1) = (x ^ 2 + 1) * ((x + 1) * (x ^ 3 + 1)) := by ring
    _ ≤ (x ^ 2 + 1) * (2 * (x ^ 4 + 1)) := by gcongr
    _ = 2 * ((x ^ 2 + 1) * (x ^ 4 + 1)) := by ring
    _ ≤ 2 * (2 * (x ^ 6 + 1)) := by gcongr
    _ = 4 * (x ^ 6 + 1) := by ring
