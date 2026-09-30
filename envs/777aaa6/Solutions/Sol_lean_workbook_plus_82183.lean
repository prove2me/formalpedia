-- Prove2me | solution 1 for lean_workbook_plus_82183
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:08:09.510427+00:00
-- url     : https://prove2.me/submissions/1eba858a-55d0-4427-b663-de7144607e4e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (x y z : ℝ) (h₁ : x + y + z = 2)
    (h₂ : x * y + y * z + z * x = 1) :
    x ∈ Set.Icc 0 (4 / 3) ∧ y ∈ Set.Icc 0 (4 / 3) ∧ z ∈ Set.Icc 0 (4 / 3) := by
  have hx : 3 * x ^ 2 ≤ 4 * x := by nlinarith [sq_nonneg (y - z)]
  have hy : 3 * y ^ 2 ≤ 4 * y := by nlinarith [sq_nonneg (z - x)]
  have hz : 3 * z ^ 2 ≤ 4 * z := by nlinarith [sq_nonneg (x - y)]
  constructor
  · constructor <;> nlinarith [sq_nonneg x, sq_nonneg (x - 4 / 3)]
  constructor
  · constructor <;> nlinarith [sq_nonneg y, sq_nonneg (y - 4 / 3)]
  · constructor <;> nlinarith [sq_nonneg z, sq_nonneg (z - 4 / 3)]

#print axioms solution
