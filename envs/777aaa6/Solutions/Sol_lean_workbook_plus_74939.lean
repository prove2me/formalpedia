-- Prove2me | solution 1 for lean_workbook_plus_74939
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:48.880254+00:00
-- url     : https://prove2.me/submissions/9be80be3-87a5-4638-b975-ce10b3b97158

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ s : ℝ, s^2 - 3 * s + 9 / 4 ≥ 0 ↔ (s - 3 / 2)^2 ≥ 0 := by
  (intros; ring)
