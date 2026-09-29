-- Prove2me | solution 1 for lean_workbook_plus_43014
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:21.628425+00:00
-- url     : https://prove2.me/submissions/9e82b18e-1c41-4605-9648-421c4b555007

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) : x = a / (-a + b + c) ∧ y = b / (a - b + c) ∧ z = c / (a + b - c) ↔ x = a / (-a + b + c) ∧ y = b / (a - b + c) ∧ z = c / (a + b - c) := by
  norm_num
