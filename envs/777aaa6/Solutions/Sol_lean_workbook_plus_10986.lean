-- Prove2me | solution 1 for lean_workbook_plus_10986
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:34.868148+00:00
-- url     : https://prove2.me/submissions/564b7f76-6784-4143-901e-6e0fa4f531bb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a₁ a₂ b₁ b₂ : ℝ) : ∃ d, d = Real.sqrt ((a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2) := by
  norm_num
