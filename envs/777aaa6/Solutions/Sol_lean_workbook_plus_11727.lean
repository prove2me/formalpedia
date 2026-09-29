-- Prove2me | solution 1 for lean_workbook_plus_11727
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:14:17.180894+00:00
-- url     : https://prove2.me/submissions/5309e09e-6d67-4e76-8cbe-cb38bf10eae3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h : x < y) : ∃ q : ℚ, x < q ∧ ↑q < y := by
  intros
  exact exists_rat_btwn h
