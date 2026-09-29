-- Prove2me | solution 1 for lean_workbook_plus_39106
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:54.540027+00:00
-- url     : https://prove2.me/submissions/b6dd6cf1-aa83-4f28-803e-b407b4214588

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (P : ℝ → ℝ) (hP : P = fun x : ℝ => a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x) : P (-5) = 1 ∧ P (-2) = 1 ∧ P 2 = 1 ∧ P 5 = 1 → P 10 = -71 := by
  intros
  grind
