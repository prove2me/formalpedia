-- Prove2me | solution 1 for lean_workbook_plus_9562
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:15.533524+00:00
-- url     : https://prove2.me/submissions/42b5a214-dbb5-47d1-b37c-f7a29a74a83d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z s : ℝ, (x^2 + y^2 + z^2 - 5 = s^2 - 6 * s + 9 → (s - 3)^2 >= 0) := by
  (intros; positivity)
