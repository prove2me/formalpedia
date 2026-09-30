-- Prove2me | solution 1 for lean_workbook_plus_76556
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:39:49.935652+00:00
-- url     : https://prove2.me/submissions/b7899c1a-fd57-40a2-94c7-9a4d9f1e861f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0)
    (h : x*y*z ≥ 1) : (x+1)*(y+1)*(z+1) ≥ 8 := by
  have h1 : 4*x ≤ (x+1)^2 := by nlinarith only [sq_nonneg (x-1)]
  have h2 : 4*y ≤ (y+1)^2 := by nlinarith only [sq_nonneg (y-1)]
  have h3 : 4*z ≤ (z+1)^2 := by nlinarith only [sq_nonneg (z-1)]
  have h12 := mul_le_mul h1 h2 (by positivity : 0 ≤ 4*y) (sq_nonneg (x+1))
  have h123 := mul_le_mul h12 h3 (by positivity : 0 ≤ 4*z)
    (by positivity : 0 ≤ (x+1)^2*(y+1)^2)
  have hs : (8:ℝ)^2 ≤ ((x+1)*(y+1)*(z+1))^2 := by
    nlinarith only [h123, h]
  exact (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 8) (by positivity)).mp hs
