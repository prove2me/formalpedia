-- Prove2me | solution 1 for lean_workbook_plus_47677
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:12.394577+00:00
-- url     : https://prove2.me/submissions/5e6206eb-44b3-4f61-b6f0-544cd36e4ec2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b) * (b + c) * (c + a) - 8 * a * b * c = 2 * c * (a - b) ^ 2 + (a + b) * (a - c) * (b - c) := by
  (intros; linarith)
