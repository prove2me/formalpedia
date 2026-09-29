-- Prove2me | solution 1 for lean_workbook_plus_44187
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:30.407789+00:00
-- url     : https://prove2.me/submissions/9ffd2cb8-6577-40bb-82be-acf7c992dd56

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : x - (0.6 * x + 6) = 2)
  (h₁ : y - (0.5 * y + 5) = x)
  (h₂ : z - (0.4 * z + 4) = y) :
  z = 90 := by
  (intros; linarith)
