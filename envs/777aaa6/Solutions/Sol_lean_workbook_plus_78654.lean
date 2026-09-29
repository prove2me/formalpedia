-- Prove2me | solution 1 for lean_workbook_plus_78654
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:59.284805+00:00
-- url     : https://prove2.me/submissions/9e2abfb9-637a-4f38-9a48-7e89ba95d30b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x = 200) (h₂ : y = 5/12 * x - 5*110/12) : y = 37.5 := by
  (intros; linarith)
