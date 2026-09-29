-- Prove2me | solution 1 for lean_workbook_plus_5912
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:05:00.708453+00:00
-- url     : https://prove2.me/submissions/e9635387-0540-4ca5-b071-10fa17bd9b4e

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x1 : ZMod 2) (x2 : ZMod 3) (x3 : ZMod 5) (hx1 : x1 ^ 2 = x1) (hx2 : x2 ^ 2 = x2) (hx3 : x3 ^ 2 = x3) : (x1 = 0 ∨ x1 = 1) ∧ (x2 = 0 ∨ x2 = 1) ∧ (x3 = 0 ∨ x3 = 1) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  constructor
  · exact eq_zero_or_one_of_sq_eq_self hx1
  constructor
  · exact eq_zero_or_one_of_sq_eq_self hx2
  · exact eq_zero_or_one_of_sq_eq_self hx3
