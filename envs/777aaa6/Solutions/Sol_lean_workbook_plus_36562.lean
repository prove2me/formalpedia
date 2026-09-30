-- Prove2me | solution 1 for lean_workbook_plus_36562
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:15:45.165811+00:00
-- url     : https://prove2.me/submissions/79c1bb5c-0ed1-43a9-95b6-a8146ffa2653

import Mathlib

set_option autoImplicit false

theorem solution (x : Real) (n : Nat) (hn : n ≠ 0) :
    x / (1 + n * x ^ 2) ≤ 1 / (2 * Real.sqrt n) := by
  have hnpos : (0 : Real) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hspos : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.mpr hnpos
  have hdpos : 0 < 1 + (n : Real) * x ^ 2 := by positivity
  apply (div_le_div_iff₀ hdpos (by positivity : 0 < 2 * Real.sqrt (n : Real))).mpr
  have hsq := sq_nonneg (Real.sqrt (n : Real) * x - 1)
  simp only [sub_sq, mul_pow, Real.sq_sqrt hnpos.le, one_pow, mul_one] at hsq
  nlinarith

#print axioms solution
