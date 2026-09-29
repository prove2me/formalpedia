-- Prove2me | solution 1 for lean_workbook_plus_34280
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:02.573964+00:00
-- url     : https://prove2.me/submissions/a8da8c56-411f-455b-9a2a-79424772bb0c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x b k : ℤ)
  (h₀ : x - 1 = 2 * k)
  (h₁ : x + 1 = 2 * k + 2)
  (h₂ : 8 * b = 4 * k * (k + 1)) :
  b = k * (k + 1) / 2 := by
  intros
  grind
