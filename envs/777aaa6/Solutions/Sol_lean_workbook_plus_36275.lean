-- Prove2me | solution 1 for lean_workbook_plus_36275
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:10.267419+00:00
-- url     : https://prove2.me/submissions/29602203-1cae-49be-9c89-58bb2efbbd0b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℕ → ℝ) (a_def : ∀ n, a n = Real.sqrt (n * (n + 1))) : a 1 = Real.sqrt 2 := by
  intros
  grind
