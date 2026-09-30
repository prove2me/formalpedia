-- Prove2me | solution 1 for lean_workbook_plus_75242
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:23.595266+00:00
-- url     : https://prove2.me/submissions/cee4f59f-babf-420f-838f-d253c149fe44

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) (f : ℝ → ℝ) (h₀ : f x = 0)
    (h₁ : f x = x ^ 2 * (x - 4) ^ 2 - 16 * (2 * x + 1) ^ 2) :
    x ^ 2 + 4 * x + 4 = 0 ∨ x ^ 2 - 12 * x - 4 = 0 := by
  apply mul_eq_zero.mp
  calc
    (x ^ 2 + 4 * x + 4) * (x ^ 2 - 12 * x - 4) =
        x ^ 2 * (x - 4) ^ 2 - 16 * (2 * x + 1) ^ 2 := by ring
    _ = f x := h₁.symm
    _ = 0 := h₀
