-- Prove2me | solution 1 for lean_workbook_plus_14746
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:59.694645+00:00
-- url     : https://prove2.me/submissions/668a6bdc-718d-4906-bef6-96169afbd3c6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ)
  (h₀ : (∀ x, (f x)^2 = 2 * f x)) :
  f 2 = 0 ∨ f 2 = 2 := by
  intros
  grind
