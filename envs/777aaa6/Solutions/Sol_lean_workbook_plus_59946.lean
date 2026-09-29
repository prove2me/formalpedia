-- Prove2me | solution 1 for lean_workbook_plus_59946
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:20.79772+00:00
-- url     : https://prove2.me/submissions/f2cd852e-40a2-450d-8207-4cd601940e0f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 ≥ 1 / 3 * (a / (b + c) + b / (c + a) + c / (a + b)) ^ 2 := by
  intro a b c
  nlinarith [sq_nonneg (a/(b+c)-b/(c+a)), sq_nonneg (b/(c+a)-c/(a+b)), sq_nonneg (c/(a+b)-a/(b+c))]
