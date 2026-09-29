-- Prove2me | solution 1 for lean_workbook_plus_77089
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:03:23.503299+00:00
-- url     : https://prove2.me/submissions/249ed32e-6ed1-4dce-ab4e-cec033609fa4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b d x y : ℤ) (h₁ : d = gcd a b) : d ∣ a * x + b * y := by
  rw [h₁]
  exact dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left a b) x) (dvd_mul_of_dvd_left (gcd_dvd_right a b) y)
