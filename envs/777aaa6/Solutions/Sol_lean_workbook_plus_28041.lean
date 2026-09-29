-- Prove2me | solution 1 for lean_workbook_plus_28041
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:56:05.215818+00:00
-- url     : https://prove2.me/submissions/358c65fd-5c42-4422-bfe1-360df1a02409

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b α β : ℝ) : ∃ A B : ℝ × ℝ, A = (Real.sqrt (α ^ 2 + β ^ 2) + a, b) ∧ B = (-Real.sqrt (α ^ 2 + β ^ 2) + a, b) := by
  norm_num
