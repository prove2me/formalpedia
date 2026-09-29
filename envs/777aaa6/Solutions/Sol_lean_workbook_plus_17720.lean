-- Prove2me | solution 1 for lean_workbook_plus_17720
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:44:19.969533+00:00
-- url     : https://prove2.me/submissions/c565d6d1-77b0-4e5a-8209-609db9d77a1c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c m n : ℤ) (h₁ : a = m^2 - n^2) (h₂ : b = 2*m*n) (h₃ : c = m^2 + n^2) (h₄ : Int.gcd m n = 1) : c = b + (m - n)^2 := by
  (intros; linarith)
