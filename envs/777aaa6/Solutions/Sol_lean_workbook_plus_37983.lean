-- Prove2me | solution 1 for lean_workbook_plus_37983
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:45.444434+00:00
-- url     : https://prove2.me/submissions/4d5f18a5-c469-482d-95f0-94b3251a2ac3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * c) / (a + b) + (b + 2 * a) / (b + c) + (c + 2 * b) / (c + a) ≥ 9 / 2 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
