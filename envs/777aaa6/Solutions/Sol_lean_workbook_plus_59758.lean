-- Prove2me | solution 1 for lean_workbook_plus_59758
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:38.881993+00:00
-- url     : https://prove2.me/submissions/489ca4c6-af14-45a3-bd01-027ba3b6d444

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, x^2 + y^2 + z^2 = 1 → (x + y + z)^2 - 2 * (x * y + y * z + z * x) = 1 := by
  (intros; linarith)
