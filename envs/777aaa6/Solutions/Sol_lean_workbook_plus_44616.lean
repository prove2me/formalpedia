-- Prove2me | solution 1 for lean_workbook_plus_44616
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:48.2953+00:00
-- url     : https://prove2.me/submissions/7533a74f-3c98-4803-b83d-d92316c298eb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, (x - y) * (y - z) * (z - x) = x * (y^2 - z^2) + y * (z^2 - x^2) + z * (x^2 - y^2) := by
  (intros; linarith)
