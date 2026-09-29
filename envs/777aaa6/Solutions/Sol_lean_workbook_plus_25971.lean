-- Prove2me | solution 1 for lean_workbook_plus_25971
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:37.343273+00:00
-- url     : https://prove2.me/submissions/814fec2d-e53e-47c7-98ac-439d538e9e6e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ)
  (h₀ : x^2 - x - 1 = 0) :
  x = (1 + Real.sqrt 5) / 2 ∨ x = (1 - Real.sqrt 5) / 2 := by
  intros
  grind
