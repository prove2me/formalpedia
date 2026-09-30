-- Prove2me | solution 1 for lean_workbook_plus_79698
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:50.0573+00:00
-- url     : https://prove2.me/submissions/f8a4241c-1a5d-45f3-8607-e5d27620015e

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

private theorem squared_version (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    u ^ 2 + v ^ 2 + u ^ 2 * v ^ 2 / (u + v) ^ 2 ≥ 9 * u * v / 4 := by
  have hs := mul_nonneg (sq_nonneg (u - v))
    (show 0 ≤ 4 * u ^ 2 + 7 * u * v + 4 * v ^ 2 by positivity)
  have hp : (9 * u * v / 4 - u ^ 2 - v ^ 2) * (u + v) ^ 2 ≤ u ^ 2 * v ^ 2 := by
    nlinarith [hs]
  have hdiv := (le_div_iff₀ (pow_pos (add_pos hu hv) 2)).2 hp
  linarith

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x + y + x * y / (Real.sqrt x + Real.sqrt y) ^ 2 ≥ 9 * Real.sqrt (x * y) / 4 := by
  have h := squared_version (Real.sqrt x) (Real.sqrt y)
    (Real.sqrt_pos.2 hx) (Real.sqrt_pos.2 hy)
  simpa only [Real.sq_sqrt (le_of_lt hx), Real.sq_sqrt (le_of_lt hy),
    Real.sqrt_mul (le_of_lt hx), mul_assoc] using h
