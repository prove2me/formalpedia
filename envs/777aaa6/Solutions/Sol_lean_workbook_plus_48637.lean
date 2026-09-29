-- Prove2me | solution 1 for lean_workbook_plus_48637
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:38.153256+00:00
-- url     : https://prove2.me/submissions/e9d74ab5-c3a5-40bb-8542-a620eecec2ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (1 / (a * b * (a + b) + a * b * c)) + (1 / (b * c * (b + c) + a * b * c)) + (1 / (a * c * (a + c) + a * b * c)) = (1 / (a * b * (a + b + c))) + (1 / (b * c * (a + b + c))) + (1 / (a * c * (a + b + c))) := by
  (intros; ring)
