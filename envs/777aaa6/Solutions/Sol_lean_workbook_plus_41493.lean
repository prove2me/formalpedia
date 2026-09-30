-- Prove2me | solution 1 for lean_workbook_plus_41493
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:41:00.396415+00:00
-- url     : https://prove2.me/submissions/746e167f-fc68-4bd4-aebe-fd39269121dc

import Mathlib.Analysis.Complex.Basic

theorem solution {x y z : ℝ} (hx : x + y + z = 5) (hy : x * y + y * z + z * x = 8) : 1 ≤ x ∧ x ≤ 7 / 3 ∧ 1 ≤ y ∧ y ≤ 7 / 3 ∧ 1 ≤ z ∧ z ≤ 7 / 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  nlinarith [sq_nonneg (y - z), sq_nonneg (x - z), sq_nonneg (x - y)]
