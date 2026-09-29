-- Prove2me | solution 1 for lean_workbook_plus_66237
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:00.53037+00:00
-- url     : https://prove2.me/submissions/b87befe7-5fc2-4ee8-9e91-4669b039a3af

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x * (y ^ 2 - z ^ 2) + y * (-x ^ 2 + z ^ 2) + z * (x ^ 2 - y ^ 2) = -(x - y) * (x - z) * (y - z) := by
  (intros; linarith)
