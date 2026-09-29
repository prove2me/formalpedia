-- Prove2me | solution 1 for lean_workbook_plus_10318
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:41.367682+00:00
-- url     : https://prove2.me/submissions/a78f3ff9-91ca-45e9-8054-dc8861cd1d0e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} : (1 / Real.sqrt 3 ^ 2 + 1 / Real.sqrt 3 ^ 2 + 1 / Real.sqrt 3 ^ 2) * ((3 - a) ^ 2 + (3 - b) ^ 2 + (3 - c) ^ 2) ≥ (1 / Real.sqrt 3 * (3 - a) + 1 / Real.sqrt 3 * (3 - b) + 1 / Real.sqrt 3 * (3 - c)) ^ 2 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
