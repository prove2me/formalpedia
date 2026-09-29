-- Prove2me | solution 1 for lean_workbook_plus_33549
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:07:34.683962+00:00
-- url     : https://prove2.me/submissions/951462b0-3fda-435b-b94e-2519786f8fb3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (z : ℂ) : (z^2 - 8 * (1 - Complex.I) * z + 63 - 16 * Complex.I = 0) ↔ (z = 3 + 4 * Complex.I ∨ z = 5 - 12 * Complex.I) := by
  have he : z^2-8*(1-Complex.I)*z+63-16*Complex.I = (z-(3+4*Complex.I))*(z-(5-12*Complex.I)) := by
    linear_combination (48 : ℂ) * Complex.I_sq
  rw [he,mul_eq_zero,sub_eq_zero,sub_eq_zero]
