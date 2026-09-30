-- Prove2me | solution 1 for lean_workbook_plus_28871
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:17:08.234558+00:00
-- url     : https://prove2.me/submissions/31e73f87-4929-4c87-bdf5-4e08794ac682

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

lemma even_quartic_pair (x y : ℤ) : Even (x * y * (x ^ 2 - y ^ 2)) := by
  rw [even_iff_two_dvd]
  apply Int.dvd_of_emod_eq_zero
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy
  all_goals norm_num [pow_two, Int.mul_emod, Int.sub_emod, hx, hy]

theorem solution : ∀ x y z : ℤ,
    Even (x * y * (x ^ 2 - y ^ 2) + y * z * (y ^ 2 - z ^ 2) +
      z * x * (z ^ 2 - x ^ 2)) := by
  intro x y z
  exact ((even_quartic_pair x y).add (even_quartic_pair y z)).add (even_quartic_pair z x)

#print axioms solution
