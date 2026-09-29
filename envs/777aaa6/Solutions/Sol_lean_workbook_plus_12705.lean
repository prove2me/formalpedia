-- Prove2me | solution 1 for lean_workbook_plus_12705
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:04.268808+00:00
-- url     : https://prove2.me/submissions/6831d0b6-8f3d-4073-ad3b-4f78e16eae51

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0) (hab : x + y + z = 1) : 1 / x + 1 / y + 1 / z ≥ 4 * (x + y + z) → (x * y + y * z + z * x ≥ 2 * (x + y + z)) → (Real.sqrt x + Real.sqrt y + Real.sqrt z ≤ 3 / 2 * Real.sqrt (x * y * z)) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
