-- Prove2me | solution 1 for lean_workbook_plus_45411
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:21.400415+00:00
-- url     : https://prove2.me/submissions/ccf293d6-3b78-4198-bad8-5d213796e0ab

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) : a^2 + 141 * a * b + 5476 * b^2 - 5 * a - 1346 * b + 512 ≥ 0 := by
  intros
  
  have h_identity : (a^2 + 141 * a * b + 5476 * b^2 - 5 * a - 1346 * b + 512) - (0) = (512 : ℝ) * 1 * ((1 + ((-673 / 512) * b) + ((-5 / 1024) * a)))^2 + ((2023 / 2048) : ℝ) * 1 * ((a + ((137654 / 2023) * b)))^2 + ((36090 / 2023) : ℝ) * 1 * (b)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^2 + 141 * a * b + 5476 * b^2 - 5 * a - 1346 * b + 512) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
