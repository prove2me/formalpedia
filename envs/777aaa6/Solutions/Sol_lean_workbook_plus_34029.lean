-- Prove2me | solution 1 for lean_workbook_plus_34029
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:58.638196+00:00
-- url     : https://prove2.me/submissions/f6bce89e-ad41-4bcb-ba21-084948c2f319

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : x * y + y * z + z * x ≠ 0) :
  3 * (x * y + y * z + z * x) / (x * y + y * z + z * x) = 3 := by
  (intros; simp_all)
