-- Prove2me | solution 1 for lean_workbook_plus_37315
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:11.392423+00:00
-- url     : https://prove2.me/submissions/e12ba85e-f210-44df-a9f4-3af52586028b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 2 * a ^ 3 + 2 * b ^ 3 + 2 * c ^ 3 + a ^ 2 * c + b ^ 2 * a + c ^ 2 * b >= 3 * a ^ 2 * b + 3 * b ^ 2 * c + 3 * c ^ 2 * a := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
