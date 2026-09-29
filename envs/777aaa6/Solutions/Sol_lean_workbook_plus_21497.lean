-- Prove2me | solution 1 for lean_workbook_plus_21497
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:56.832624+00:00
-- url     : https://prove2.me/submissions/bc886d4b-8889-460d-90b6-e9b023d6311e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (a - b) ^ 2 * (c - d) ^ 2 + (a * d - b * c) ^ 2 ≥ 0 := by
  (intros; positivity)
