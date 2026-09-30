-- Prove2me | solution 1 for lean_workbook_plus_50024
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:53:54.253998+00:00
-- url     : https://prove2.me/submissions/303127da-d788-423a-ac11-426030a47417

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem separated_bound (x y z : ℝ) (hxy : 1 ≤ |x-y|)
    (hyz : 1 ≤ |y-z|) (hzx : 1 ≤ |z-x|) :
    3 ≤ x^2+y^2+z^2-x*y-y*z-z*x := by
  rcases le_total 0 (x-y) with h1 | h1 <;>
    rcases le_total 0 (y-z) with h2 | h2 <;>
    rcases le_total 0 (z-x) with h3 | h3
  all_goals
    simp_all only [abs_of_nonneg, abs_of_nonpos]
    nlinarith [sq_nonneg (x-y-1), sq_nonneg (x-y+1),
      sq_nonneg (x-y-2), sq_nonneg (x-y+2),
      sq_nonneg (y-z-1), sq_nonneg (y-z+1),
      sq_nonneg (y-z-2), sq_nonneg (y-z+2),
      sq_nonneg (z-x-1), sq_nonneg (z-x+1),
      sq_nonneg (z-x-2), sq_nonneg (z-x+2)]

theorem solution (x y z : ℝ) (h₀ : 0 < abs (x-y)) (h₁ : 0 < abs (y-z))
    (h₂ : 0 < abs (z-x)) (h₃ : abs (x-y) ≥ abs (y-z))
    (h₄ : abs (y-z) ≥ abs (z-x)) (h₅ : abs (z-x) ≥ 1) :
    3 ≤ x^2+y^2+z^2-x*y-y*z-z*x :=
  separated_bound x y z (h₅.trans (h₄.trans h₃)) (h₅.trans h₄) h₅
