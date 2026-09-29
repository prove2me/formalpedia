-- Prove2me | solution 1 for lean_workbook_plus_31192
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:02.787611+00:00
-- url     : https://prove2.me/submissions/80cd17a1-0e3f-491c-95e8-9ccd887b8ec3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (9*c^3+55*c^2*b+87*a*c^2+55*a^2*c+87*c*b^2-453*a*c*b+9*b^3+87*a^2*b+9*a^3+55*a*b^2)^2 ≥ 0 := by
  (intros; positivity)
