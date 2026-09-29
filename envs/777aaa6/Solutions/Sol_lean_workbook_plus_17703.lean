-- Prove2me | solution 1 for lean_workbook_plus_17703
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:30.239655+00:00
-- url     : https://prove2.me/submissions/c8322139-cfc7-4be9-96c8-0b61adab44a0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y a t : ℝ)
  (h₀ : t = x * y)
  (h₁ : a = x + y) :
  x^3 + y^3 = a^3 - 3 * a * t := by
  intros
  grind
