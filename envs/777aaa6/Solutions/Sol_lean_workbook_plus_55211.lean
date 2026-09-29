-- Prove2me | solution 1 for lean_workbook_plus_55211
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:25.2179+00:00
-- url     : https://prove2.me/submissions/a2e57742-61e0-4120-8124-0a512a80d95d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (2 * b - c) * a ^ 2 + (2 * c - a) * b ^ 2 + (2 * a - b) * c ^ 2 >= 3 * a * b * c := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
