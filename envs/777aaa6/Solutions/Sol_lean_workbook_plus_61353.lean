-- Prove2me | solution 1 for lean_workbook_plus_61353
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:01.016015+00:00
-- url     : https://prove2.me/submissions/e8193184-be3e-434e-85f7-27041a130efe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, (1 + x) ^ 2 * (1 + y) ^ 2 * (1 + z) ^ 2 = (1 + y + z + y * z) * (1 + z + x + x * z) * (1 + x + y + x * y) := by
  (intros; linarith)
