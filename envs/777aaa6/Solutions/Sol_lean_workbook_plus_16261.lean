-- Prove2me | solution 1 for lean_workbook_plus_16261
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:24.321955+00:00
-- url     : https://prove2.me/submissions/acee1646-d625-489d-984e-1b1df4ed13eb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ y, ∑' k : ℕ, (-1 : ℝ)^(k+1) * k^2 / (1 + k^3) = y := by
  norm_num
