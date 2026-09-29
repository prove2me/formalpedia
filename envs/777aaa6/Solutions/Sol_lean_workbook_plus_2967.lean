-- Prove2me | solution 1 for lean_workbook_plus_2967
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:44.635449+00:00
-- url     : https://prove2.me/submissions/f34f4913-011b-42b7-acc7-9075f9c32d8b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (s v : ℝ)
  (h₀ : 0 < s ∧ 0 < v)
  (h₁ : v * (114 / 100) = s * (94 / 100)) :
  s / v = 57 / 47 := by
  intros
  grind
