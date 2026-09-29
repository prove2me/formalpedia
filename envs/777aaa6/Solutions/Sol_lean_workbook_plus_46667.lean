-- Prove2me | solution 1 for lean_workbook_plus_46667
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:46.133202+00:00
-- url     : https://prove2.me/submissions/868aecba-5d85-4670-8fc7-960101ed5da4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b : ℂ, a^2 - b^2 = (a + b) * (a - b) := by
  (intros; ring)
