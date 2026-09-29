-- Prove2me | solution 1 for lean_workbook_plus_13924
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:30.576913+00:00
-- url     : https://prove2.me/submissions/4993a956-2cf1-4b2d-902a-2cf2408d58e4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
  ∑' i : ℕ, x ^ i = 1 / (1 - x) := by
  simpa only [one_div] using tsum_geometric_of_abs_lt_one (by rw [abs_of_pos hx.1]; exact hx.2)
