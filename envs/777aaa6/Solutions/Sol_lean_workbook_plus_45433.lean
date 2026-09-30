-- Prove2me | solution 1 for lean_workbook_plus_45433
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:50:06.266287+00:00
-- url     : https://prove2.me/submissions/966fa4e0-a828-48a6-a1af-4a96fa48d15d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution {a b : ℂ} (hab : a ≠ b)
    (h : a ^ 4 + a + 1 = 0) (h' : b ^ 4 + b + 1 = 0) :
    a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 = -1 := by
  have hp : (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 + 1) = 0 := by
    linear_combination h - h'
  have hs := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hab)
  linear_combination hs

#print axioms solution
