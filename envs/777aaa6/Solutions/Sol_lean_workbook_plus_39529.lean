-- Prove2me | solution 1 for lean_workbook_plus_39529
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:00.226367+00:00
-- url     : https://prove2.me/submissions/107ff0f0-5751-416c-a0d4-ef726fc68f34

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p q : ℕ) (h : Nat.Coprime p q) (n : ℕ) : Nat.Coprime (p^n) (q^n) := by
  intros
  exact Nat.pow_gcd_pow_of_gcd_eq_one h
