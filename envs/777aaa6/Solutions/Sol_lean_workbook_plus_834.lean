-- Prove2me | solution 1 for lean_workbook_plus_834
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:13.438759+00:00
-- url     : https://prove2.me/submissions/ecc3fb0a-e9c3-4876-b2dc-9391dcbbb0aa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} : 2 * a ^ 2 * b * c + 2 * a * b ^ 2 * c + 2 * a * b * c ^ 2 ≤ 2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
