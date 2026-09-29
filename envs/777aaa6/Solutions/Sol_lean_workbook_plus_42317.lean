-- Prove2me | solution 1 for lean_workbook_plus_42317
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:32.366044+00:00
-- url     : https://prove2.me/submissions/142f8398-7a26-44a1-96b4-2ef7bff83599

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (habc : a = 1 ∧ b = -16 ∧ c = 60) : b^2 - 4*a*c = 16^2 - 4*1*60 := by
  (intros; simp_all)
