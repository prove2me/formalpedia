-- Prove2me | solution 1 for lean_workbook_plus_40220
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:40.850821+00:00
-- url     : https://prove2.me/submissions/48e64bab-8880-4d14-b1e5-594cea09dce0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ): f 0 = 0 → f (f 0) = 0 := by
  (intros; simp_all)
