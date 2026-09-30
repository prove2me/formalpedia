-- Prove2me | solution 1 for lean_workbook_plus_26233
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:58:12.645771+00:00
-- url     : https://prove2.me/submissions/c54c5b68-7e8c-4f33-ade3-75d405432e1e

import Mathlib
set_option autoImplicit false

theorem solution (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : (3 * (1 + t) * (1 - 2 * t) ^ 2 * t ^ 2) / (1 + 2 * t) / (1 - t) ≥ 0   := by
  have ht0 : 0 <= t := ht.1
  have hd1 : 0 < 1 + 2 * t := by linarith
  have hd2 : 0 < 1 - t := by linarith [ht.2]
  have hn : 0 <= 3 * (1 + t) * (1 - 2 * t)^2 * t^2 := by positivity
  exact div_nonneg (div_nonneg hn hd1.le) hd2.le

#print axioms solution
