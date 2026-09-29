-- Prove2me | solution 1 for lean_workbook_plus_7691
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:10.904893+00:00
-- url     : https://prove2.me/submissions/c7e7c7f5-3ca2-4016-ac8d-35323cfd084b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*(a^2 + b^2 + c^2 - a*b - a*c - b*c) := by
  (intros; linarith)
