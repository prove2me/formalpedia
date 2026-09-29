-- Prove2me | solution 1 for lean_workbook_plus_62541
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:27.215226+00:00
-- url     : https://prove2.me/submissions/1acf6028-c2c2-4d2f-8df9-fbdfed8e60f8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a : ℝ, 1/3 ≤ a ∧ a ≤ 1 → (a-1)*(2*a^3 + 2*a^2 + 3*a - 1) ≤ 0 := by
  intro a h
  have ha : 0 ≤ a := by linarith [h.1]
  have hp : 0 ≤ 2*a^3 + 2*a^2 + 3*a - 1 := by
    nlinarith [pow_nonneg ha 3, sq_nonneg a, h.1]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith [h.2]) hp
