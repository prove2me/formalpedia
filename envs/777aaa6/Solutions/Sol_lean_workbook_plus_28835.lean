-- Prove2me | solution 1 for lean_workbook_plus_28835
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:56.169637+00:00
-- url     : https://prove2.me/submissions/ca550d4c-38ac-460e-8402-2061d208147a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d k m : ℤ)
  (h₀ : a + c = 3 * k)
  (h₁ : b + d = 3 * m)
  (h₂ : b^2 - a * c = c^2 - b * d) :
  b * d - a * c = (c - b) * (c + b) := by
  (intros; linarith)
