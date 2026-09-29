-- Prove2me | solution 1 for lean_workbook_plus_19574
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:33.792624+00:00
-- url     : https://prove2.me/submissions/cbb90f7d-3d13-46fa-816f-69b68c062acc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (P : ℝ) : (3 * P / 2) * (1 / 2) = 3 * P / 4 := by
  (intros; linarith)
