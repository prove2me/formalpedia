-- Prove2me | solution 1 for lean_workbook_plus_50554
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:23.637332+00:00
-- url     : https://prove2.me/submissions/1ee67ea4-2d56-4398-8a83-06474b817eb3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a : ℝ) (ha : a ≥ 0) : a + 1 ≥ 2 * Real.sqrt a := by
  nlinarith [sq_nonneg (Real.sqrt a - 1), Real.sq_sqrt ha]
