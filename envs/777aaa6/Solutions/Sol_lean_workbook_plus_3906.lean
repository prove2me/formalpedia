-- Prove2me | solution 1 for lean_workbook_plus_3906
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:51.950569+00:00
-- url     : https://prove2.me/submissions/1d7105e6-f0a8-4fc6-857e-a4b803f18c4f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b : ℝ) : ∃ x y z : ℝ, y = b ∧ x = (-1/2 * z^2 + (3 * b + 1) / 2) := by
  simp
