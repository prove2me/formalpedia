-- Prove2me | solution 1 for lean_workbook_plus_969
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:13:58.488216+00:00
-- url     : https://prove2.me/submissions/59e462dc-6cb9-4d1e-b9cf-76e424606ce6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) : (1 / x + 1 / y + 1 / z) ^ 2 ≥ 3 * (1 / (x * y) + 1 / (y * z) + 1 / (z * x)) := by
  simp only [one_div, mul_inv_rev]
  nlinarith only [sq_nonneg (x⁻¹-y⁻¹), sq_nonneg (y⁻¹-z⁻¹), sq_nonneg (z⁻¹-x⁻¹)]
