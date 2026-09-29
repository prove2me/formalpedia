-- Prove2me | solution 1 for lean_workbook_plus_65403
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:52.87841+00:00
-- url     : https://prove2.me/submissions/28d5bf3c-c2eb-4db4-8418-1679b288cf46

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℕ) (hx : 1 < x) : (x - 1) ∣ (x^y - 1) := by
  intros
  exact Nat.sub_one_dvd_pow_sub_one x y
