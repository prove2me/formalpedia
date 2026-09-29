-- Prove2me | solution 1 for lean_workbook_plus_32269
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:02.754932+00:00
-- url     : https://prove2.me/submissions/e51499f1-59b6-4af8-884a-b3b9d10c50fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℂ) : (x - y) ^ 5 + (y - z) ^ 5 + (z - x) ^ 5 = -5 * (x - y) * (x - z) * (y - z) * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - x * z - y * z) := by
  (intros; ring)
