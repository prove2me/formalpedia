-- Prove2me | solution 1 for lean_workbook_plus_20697
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:10.72348+00:00
-- url     : https://prove2.me/submissions/01dd1093-e670-41ea-b13b-c3535f225eb2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + c = 2 * b) :
  1 / (Real.sqrt a + Real.sqrt b) + 1 / (Real.sqrt b + Real.sqrt c) =
    2 / (Real.sqrt a + Real.sqrt c) := by
  intros
  grind
