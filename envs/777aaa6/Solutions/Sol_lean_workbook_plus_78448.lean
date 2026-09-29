-- Prove2me | solution 1 for lean_workbook_plus_78448
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:41.08017+00:00
-- url     : https://prove2.me/submissions/2929b2e0-7480-4981-a436-e151d2fffe38

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x₁ x₂ m p : ℤ) (h₁ : x₁ * x₂ = p^2 + 1) (h₂ : x₁ + x₂ = -2*m) : p^4 + 4*m^2 = (x₁^2 + 1)*(x₂^2 + 1) := by
  intros
  grind
