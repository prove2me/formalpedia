-- Prove2me | solution 1 for lean_workbook_plus_25229
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:12:23.712376+00:00
-- url     : https://prove2.me/submissions/a4aeaf6b-68b5-4192-9b6c-974be23e7601

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 + x * y + y ^ 2 ≤ 3 * (x - Real.sqrt (x * y) + y) ^ 2 := by
  have hs := Real.sq_sqrt (mul_nonneg hx hy)
  have hu0 := Real.sqrt_nonneg (x * y)
  have hu : Real.sqrt (x * y) ≤ (x + y) / 2 := by
    apply Real.sqrt_le_iff.2
    exact ⟨by linarith, by nlinarith [sq_nonneg (x - y)]⟩
  have h1 : 0 ≤ x + y - Real.sqrt (x * y) := by linarith
  have h2 : 0 ≤ x + y - 2 * Real.sqrt (x * y) := by linarith
  nlinarith [mul_nonneg h1 h2]
