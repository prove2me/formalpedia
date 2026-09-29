-- Prove2me | solution 1 for lean_workbook_plus_32298
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:59.364207+00:00
-- url     : https://prove2.me/submissions/0e72ca09-4210-4da3-8bcb-79bf33868283

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 2 * a * b - 2 * b * c - 2 * c * a) - (a * b + b * c + c * a + a * b * c - 4) = 3 * (a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 2 * a * b - 2 * b * c - 2 * c * a) - (a * b + b * c + c * a + a * b * c - 4) := by
  norm_num
