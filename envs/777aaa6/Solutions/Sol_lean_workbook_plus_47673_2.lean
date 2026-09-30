-- Prove2me | solution 2 for lean_workbook_plus_47673
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:06.874576+00:00
-- url     : https://prove2.me/submissions/164bc1ef-b5a5-4136-a388-d8e4c4c82530

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℕ) (hab : Nat.Coprime a b) (n : ℕ) : Nat.Coprime a (b^n) := by
  intros
  exact Nat.gcd_pow_right_of_gcd_eq_one hab
