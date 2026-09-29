-- Prove2me | solution 1 for lean_workbook_plus_2123
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:39.125338+00:00
-- url     : https://prove2.me/submissions/c35fb0a4-844e-4b04-a5b8-c6478a1d1260

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) : x^3 < 1 ∧ 1 < x^4 + 1 := by
  intros
  simp_all <;> nlinarith [sq_nonneg x]
