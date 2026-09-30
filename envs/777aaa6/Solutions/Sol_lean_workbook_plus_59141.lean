-- Prove2me | solution 1 for lean_workbook_plus_59141
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:23:55.808591+00:00
-- url     : https://prove2.me/submissions/6bb44531-962a-44d2-940c-24d6d255d013

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

theorem solution (ω : ℂ) (h : ω ^ 3 = 1) (h' : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  have hp : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr h')

#print axioms solution
