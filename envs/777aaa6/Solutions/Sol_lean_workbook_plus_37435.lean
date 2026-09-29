-- Prove2me | solution 1 for lean_workbook_plus_37435
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:41:40.629947+00:00
-- url     : https://prove2.me/submissions/d89d608f-40a0-429d-a247-d25696a68c56

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x + 2 < 0 ↔ x < -2 := by
  intros
  exact Iff.symm lt_neg_iff_add_neg
