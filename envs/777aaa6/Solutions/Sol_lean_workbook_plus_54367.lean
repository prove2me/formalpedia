-- Prove2me | solution 1 for lean_workbook_plus_54367
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:39.806878+00:00
-- url     : https://prove2.me/submissions/24f94de8-15b9-4b4b-8a73-08fd2fc35e9f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ¬∃ x : ℝ, x > 0 ∧ x ^ 6 + x ^ 4 + x ^ 2 + x + 3 = 0 := by
  rintro ⟨x,hx,h⟩
  have hp : 0<x^6+x^4+x^2+x+3 := by positivity
  linarith
