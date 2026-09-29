-- Prove2me | solution 1 for lean_workbook_plus_21844
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:19.546023+00:00
-- url     : https://prove2.me/submissions/a4ea764d-552d-4b49-a86b-f62fe6b87722

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z w : ℝ)
  (h₀ : 10^(-2:ℤ) * (x + y + z + w) = 7.11)
  (h₁ : (10^(-2:ℤ) * x) * (10^(-2:ℤ) * y) * (10^(-2:ℤ) * z) * (10^(-2:ℤ) * w) = 7.11) :
  x * y * z * w = 711000000 := by
  (intros; linarith)
