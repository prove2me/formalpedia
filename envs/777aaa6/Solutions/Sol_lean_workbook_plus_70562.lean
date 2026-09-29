-- Prove2me | solution 1 for lean_workbook_plus_70562
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:02.252991+00:00
-- url     : https://prove2.me/submissions/3c69699b-8819-4e6e-9691-663f119ffd4c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) :
  Real.sqrt (a * b * ((a^2 + b^2) / 2)) ≤ ((a + b) / 2)^2 := by
  intros
  apply Real.sqrt_le_iff.2
  constructor
  · positivity
  · nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
