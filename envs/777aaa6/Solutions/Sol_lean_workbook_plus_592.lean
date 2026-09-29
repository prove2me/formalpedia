-- Prove2me | solution 1 for lean_workbook_plus_592
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:51.58756+00:00
-- url     : https://prove2.me/submissions/71261ed7-bfd1-4a36-a38c-eb5a2c634d46

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x + y + z = 5) (h₂ : x*y + y*z + z*x = 3): x + y + z ≤ 5 ∧ x*y + y*z + z*x = 3 := by
  (intros; simp_all)
