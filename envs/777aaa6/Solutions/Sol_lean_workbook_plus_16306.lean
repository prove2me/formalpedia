-- Prove2me | solution 1 for lean_workbook_plus_16306
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:04.930989+00:00
-- url     : https://prove2.me/submissions/203f29d0-ff62-4283-bd3d-99e0ef88b12c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 4 + b ^ 4 + c ^ 4 + 2 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) ≥ 6 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) - 3 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  intros
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - b^3), sq_nonneg (a^2 - c^2), sq_nonneg (a^3 - c^3), sq_nonneg (b^2 - c^2), sq_nonneg (b^3 - c^3)]
