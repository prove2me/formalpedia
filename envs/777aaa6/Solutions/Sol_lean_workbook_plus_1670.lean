-- Prove2me | solution 1 for lean_workbook_plus_1670
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:10:53.360717+00:00
-- url     : https://prove2.me/submissions/d8d9510e-ed47-46af-b1d0-808201172c4f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : x ≠ 0 ∧ y ≠ 0) (h₂ : x * y = 3) (h₃ : x / y + y / x = 4) : x * y * (x + y) ^ 2 - 2 * x ^ 2 * y ^ 2 = 36 := by
  intros
  grind
