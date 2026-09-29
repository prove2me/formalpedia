-- Prove2me | solution 1 for lean_workbook_plus_35572
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:47.456177+00:00
-- url     : https://prove2.me/submissions/a073ae08-d201-44e2-9bbb-91feac6f2a93

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℂ, (a^2*c + b^2*a + c^2*b - a^2*b - b^2*c - c^2*a) = (b - a) * (c - a) * (c - b) := by
  (intros; ring)
