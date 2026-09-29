-- Prove2me | solution 1 for lean_workbook_plus_39152
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:34.655131+00:00
-- url     : https://prove2.me/submissions/451dd889-ac31-417f-ac5f-597907281638

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :  ∀ a b c : ℝ, (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ (8/9) * (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) := by
  intro a b c
  intros
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - b^3), sq_nonneg (a^2 - c^2), sq_nonneg (a^3 - c^3), sq_nonneg (b^2 - c^2), sq_nonneg (b^3 - c^3)]
