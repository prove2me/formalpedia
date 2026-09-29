-- Prove2me | solution 1 for lean_workbook_plus_7912
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:40.954907+00:00
-- url     : https://prove2.me/submissions/739c856e-72e7-4f05-a332-41b4b154f4ea

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b : ℝ, (a^2 - a + 1) * (b^2 - b + 1) ≥ (a^2 + b^2) / 2 ∧ (a^2 + b^2) / 2 ≥ (a^2 + a*b + b^2) / 3 := by
  intro a b
  constructor
  · nlinarith only [sq_nonneg (a*b-(a+b)/2),sq_nonneg ((a+b)/2-1)]
  · nlinarith only [sq_nonneg (a-b)]
