-- Prove2me | solution 1 for lean_workbook_plus_23029
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:47:11.432743+00:00
-- url     : https://prove2.me/submissions/896515ad-0cff-44c9-8be1-138893a6474f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≠ 0) : (x + 1/x) * ((x + 1/x)^2 - 3) = x^3 + 1/(x^3) := by
  (intros; field_simp; ring)
