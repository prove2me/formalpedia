-- Prove2me | solution 1 for lean_workbook_plus_16234
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:35.490049+00:00
-- url     : https://prove2.me/submissions/8fad375a-757a-4d68-9ad0-f8616673de37

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a : ℝ) (ha : 0 ≤ a) : Real.sqrt a ≤ (1 + a) / 2 := by
  nlinarith [sq_nonneg (1 - Real.sqrt a), Real.sq_sqrt ha]
