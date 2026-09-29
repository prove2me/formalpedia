-- Prove2me | solution 1 for lean_workbook_plus_30749
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:45.295512+00:00
-- url     : https://prove2.me/submissions/464f1d59-13e8-4012-86dc-debc6e07ed72

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (hab : a < b) : ∃ q : ℚ, a < q ∧ ↑q < b := by
  intros
  exact?
