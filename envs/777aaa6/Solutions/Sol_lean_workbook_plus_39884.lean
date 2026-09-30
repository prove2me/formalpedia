-- Prove2me | solution 1 for lean_workbook_plus_39884
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:13:25.557631+00:00
-- url     : https://prove2.me/submissions/2f1868da-6240-4091-8923-af31ce24fb68

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x : ℝ, x ∈ Set.Icc 0 1 → x * (x ^ 3 - 6 * x + 9) ≤ 4   := by
  intro x hx
  have h1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have h3 : 0 ≤ x + 3 := by linarith only [hx.1]
  have hgap : 4 - x * (x ^ 3 - 6 * x + 9) = (1 - x) + (1 - x)^3 * (x + 3) := by ring
  apply sub_nonneg.mp
  rw [hgap]
  exact add_nonneg h1 (mul_nonneg (pow_nonneg h1 3) h3)

#print axioms solution
