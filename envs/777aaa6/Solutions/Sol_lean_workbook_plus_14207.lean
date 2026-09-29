-- Prove2me | solution 1 for lean_workbook_plus_14207
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:47.266148+00:00
-- url     : https://prove2.me/submissions/9e3f1239-d3c7-45f0-a306-3f6d11ab4e39

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z p : ℝ)
  (h₀ : p = x * y * z)
  (h₁ : x * (p - 3) = -1)
  (h₂ : y * (p - 5) = -2)
  (h₃ : z * (p - 2) = -4) :
  p^4 - 10 * p^3 + 31 * p^2 - 30 * p + 8 = 0 := by
  intros
  grind
