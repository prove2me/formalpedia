-- Prove2me | solution 1 for lean_workbook_plus_77963
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:25.159842+00:00
-- url     : https://prove2.me/submissions/e522b021-35c9-4141-93fa-a5c7055a39f6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ)
  (h₀ : a + b = 1)
  (h₁ : a + b + c = 1)
  (h₂ : b + c + d = 1)
  (h₃ : c + d = 1) :
  a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1 := by
  (intros; simp_all)
