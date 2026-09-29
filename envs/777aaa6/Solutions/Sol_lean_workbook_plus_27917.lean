-- Prove2me | solution 1 for lean_workbook_plus_27917
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:06:11.644996+00:00
-- url     : https://prove2.me/submissions/fdf0b2ee-8211-43b4-b715-190da605a1fc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m e γ k r : ℝ) : (k * e ^ 2) / (γ * m ^ 2) = (k * e ^ 2) / (γ * m ^ 2) := by
  norm_num
