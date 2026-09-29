-- Prove2me | solution 1 for lean_workbook_plus_75684
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:06.530371+00:00
-- url     : https://prove2.me/submissions/7c214ed6-5efe-4eac-9f85-aa398410d2bd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a^3 + b^3 + c^3 - 3 * a * b * c)^2 ≤ (a^2 + b^2 + c^2)^3 := by
  intros
  
  have h_identity : ((a^2 + b^2 + c^2)^3) - ((a^3 + b^3 + c^3 - 3 * a * b * c)^2) = (3 : ℝ) * 1 * (((b * (a ^ 2)) + (c * (a ^ 2)) + ((-1 / 3) * a * (b ^ 2)) + ((-1 / 3) * a * (c ^ 2)) + ((-1 / 3) * b * (c ^ 2)) + ((-1 / 3) * c * (b ^ 2)) + ((1 / 3) * a * b * c)))^2 + ((8 / 3) : ℝ) * 1 * (((a * (b ^ 2)) + (c * (b ^ 2)) + ((-1 / 2) * a * (c ^ 2)) + ((-1 / 2) * b * (c ^ 2)) + ((1 / 2) * a * b * c)))^2 + (2 : ℝ) * 1 * (((a * (c ^ 2)) + (b * (c ^ 2)) + (a * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2 + c^2)^3) - ((a^3 + b^3 + c^3 - 3 * a * b * c)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
