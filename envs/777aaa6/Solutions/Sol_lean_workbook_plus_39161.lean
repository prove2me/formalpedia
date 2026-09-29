-- Prove2me | solution 1 for lean_workbook_plus_39161
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:55.19623+00:00
-- url     : https://prove2.me/submissions/70851ef1-45d5-4279-9dba-d2081e3c7292

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 2 * (a * b^2 + b * c^2 + c * a^2) ≥ a^2 * b + b^2 * c + c^2 * a + 3 * a * b * c := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
