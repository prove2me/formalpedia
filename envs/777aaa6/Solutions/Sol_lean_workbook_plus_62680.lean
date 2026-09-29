-- Prove2me | solution 1 for lean_workbook_plus_62680
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:22:34.05704+00:00
-- url     : https://prove2.me/submissions/be086083-eed7-4ba7-aa70-38f74cf26764

import Theorems.Thm_lean_workbook_plus_62680
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (x : ℝ) (a b : ℝ) (h₀ : x = a * b) (h₁ : a + b = 2) :
    x * (3 - 2 * x) ≤ 9 / 8 := by
  nlinarith [sq_nonneg (4 * x - 3)]
