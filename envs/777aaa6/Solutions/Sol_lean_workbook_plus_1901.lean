-- Prove2me | solution 1 for lean_workbook_plus_1901
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:22.651818+00:00
-- url     : https://prove2.me/submissions/b3e6c2b0-3a72-48ca-99ad-c3ed2ea8e4ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 + 2*a*b*c + 1 - 2*(a*b + b*c + a*c) = (a-1)^2 + (b-1)^2 + (c-1)^2 + 2*(a-1)*(b-1)*(c-1) := by
  (intros; linarith)
