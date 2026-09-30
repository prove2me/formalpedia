-- Prove2me | solution 1 for lean_workbook_plus_29329
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:03:23.31313+00:00
-- url     : https://prove2.me/submissions/6b23ac79-0835-4c1d-a2da-463fe784e712

import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (x y : ℝ) (h₀ : 0 ≤ x ∧ 0 ≤ y) :
    ((x + y) / 2)^5 ≤ (x^5 + y^5) / 2 := by
  have hc := (convexOn_pow (𝕜 := ℝ) 5).2 h₀.1 h₀.2
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (by norm_num)
  simp only [smul_eq_mul] at hc
  convert hc using 1 <;> ring

#print axioms solution
