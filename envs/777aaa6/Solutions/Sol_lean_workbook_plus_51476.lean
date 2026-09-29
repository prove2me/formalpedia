-- Prove2me | solution 1 for lean_workbook_plus_51476
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:06:15.52301+00:00
-- url     : https://prove2.me/submissions/04d4e9a3-6ab6-4a55-a70f-e9ead406bb71

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h : a ≠ 0) : (a⁻¹)⁻¹ = a := by
  norm_num
