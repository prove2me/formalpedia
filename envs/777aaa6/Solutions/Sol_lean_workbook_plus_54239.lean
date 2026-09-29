-- Prove2me | solution 1 for lean_workbook_plus_54239
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:01.727292+00:00
-- url     : https://prove2.me/submissions/272b4e96-523a-4fdc-8db0-b8423dfeb1ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, 2 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x + x * y * z) ≥ (x + y) * (y + z) * (z + x) + (x - y) * (x - z) * (y - z) := by
  (intros; linarith)
