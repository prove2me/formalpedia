-- Prove2me | solution 1 for lean_workbook_plus_73836
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:27.955565+00:00
-- url     : https://prove2.me/submissions/22e5442e-9ade-4c41-8966-dbb56217dc95

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : (1 / c + 1 / a) / 2 ≥ 2 / (c + a) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg (a - c)]
