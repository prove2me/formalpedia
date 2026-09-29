-- Prove2me | solution 1 for lean_workbook_plus_82259
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:40.660303+00:00
-- url     : https://prove2.me/submissions/26002f3e-66dd-4493-90d2-95a4bb3cf0cd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x + (390 - x) / 3 = 174) :
  x = 66 := by
  (intros; linarith)
