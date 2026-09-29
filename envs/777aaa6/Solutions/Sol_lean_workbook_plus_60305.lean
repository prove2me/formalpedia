-- Prove2me | solution 1 for lean_workbook_plus_60305
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:34:03.213128+00:00
-- url     : https://prove2.me/submissions/141fb653-0fe4-4abd-9526-1dc5ed386cc0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 - 2 * a * b + b^2 - 2 * b * c + c^2 - 2 * c * a)^2 ≥ 0 := by
  (intros; positivity)
