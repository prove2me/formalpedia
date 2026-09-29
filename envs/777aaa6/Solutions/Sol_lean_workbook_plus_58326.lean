-- Prove2me | solution 1 for lean_workbook_plus_58326
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:35.424022+00:00
-- url     : https://prove2.me/submissions/616f722c-d495-482e-b56c-518d18486846

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : x ≥ 0 ∧ y ≥ 0) (h₂ : x ^ 2 + y ^ 2 = 1) : x + y ≤ Real.sqrt 2 := by
  intros
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
