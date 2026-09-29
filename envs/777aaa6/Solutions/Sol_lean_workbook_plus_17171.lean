-- Prove2me | solution 1 for lean_workbook_plus_17171
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:39.645718+00:00
-- url     : https://prove2.me/submissions/0207d976-6f20-4a73-9f88-96d63045d42e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) : (a * x + b * y + c * z) ^ 2 + (a * y - b * x) ^ 2 + (b * z - c * y) ^ 2 + (c * x - a * z) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
  (intros; linarith)
