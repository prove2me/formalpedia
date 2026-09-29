-- Prove2me | solution 1 for lean_workbook_plus_60671
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:17.212671+00:00
-- url     : https://prove2.me/submissions/2aef5a01-86da-4a20-88fc-7421d2194c37

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c p : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hp : p ≥ 0) : (a^2 + b^2 + c^2) * (p - 1)^2 / 2 ≥ (a * b + b * c + c * a) * (p - 1)^2 / 2 := by
  intros
  
  have h_identity : ((a^2 + b^2 + c^2) * (p - 1)^2 / 2) - ((a * b + b * c + c * a) * (p - 1)^2 / 2) = ((1 / 2) : ℝ) * 1 * ((a + ((-1 / 2) * b) + ((-1 / 2) * c) + ((1 / 2) * b * p) + ((1 / 2) * c * p) + ((-1) * a * p)))^2 + ((3 / 8) : ℝ) * 1 * ((b + ((-1) * c) + (c * p) + ((-1) * b * p)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2 + c^2) * (p - 1)^2 / 2) - ((a * b + b * c + c * a) * (p - 1)^2 / 2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
