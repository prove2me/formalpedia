-- Prove2me | solution 1 for lean_workbook_plus_29316
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:30.764482+00:00
-- url     : https://prove2.me/submissions/28cbe84a-9261-4a5b-b769-169632cba361

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x^6 - 1)^2 + (x^5 - x)^2 + (x^4 - x^2)^2 + 1 ≥ 0 := by
  (intros; positivity)
