-- Prove2me | solution 1 for lean_workbook_plus_54784
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:30:24.07641+00:00
-- url     : https://prove2.me/submissions/060b6d35-9c32-4d34-8636-c4ae4db51f30

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : y ≠ x)
  (h₂ : y ≠ z)
  (h₃ : z ≠ x)
  (h₄ : x + y + z = 1) :
  4 * x * y * z * (x * y + y * z + z * x) * (x + y + z) ≤ (z * x * (x + y + z) + y * (x * y + y * z + z * x))^2 := by
  nlinarith only [sq_nonneg (z*x*(x+y+z)-y*(x*y+y*z+z*x))]
