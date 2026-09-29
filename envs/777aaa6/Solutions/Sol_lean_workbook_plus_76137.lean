-- Prove2me | solution 1 for lean_workbook_plus_76137
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:49.048741+00:00
-- url     : https://prove2.me/submissions/cb326587-ef95-46c4-8cd6-c8aecaa1d202

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a * (b + c - a) ^ 2 + b * (a + c - b) ^ 2 + c * (a + b - c) ^ 2 ≥ 3 * a * b * c := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
