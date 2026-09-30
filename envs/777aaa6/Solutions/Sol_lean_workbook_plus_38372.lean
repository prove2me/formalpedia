-- Prove2me | solution 1 for lean_workbook_plus_38372
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:35.719155+00:00
-- url     : https://prove2.me/submissions/fc9eb296-59d8-4b19-938f-353989078c03

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

theorem solution (A : Type*) [Ring A] (h : ∀ x : A, x ^ 2 = x) :
    ∀ x : A, x + x = 0 := by
  intro x
  have hx : x = -x := by simpa only [neg_sq, h x] using h (-x)
  exact eq_neg_iff_add_eq_zero.mp hx

theorem multiplication_commutes (A : Type*) [Ring A] (h : ∀ x : A, x ^ 2 = x)
    (x y : A) : x * y = y * x := by
  have hsum : x * y + y * x = 0 := by
    calc
      x * y + y * x = (x + y) ^ 2 - x ^ 2 - y ^ 2 := by noncomm_ring
      _ = 0 := by rw [h, h, h]; abel
  exact (eq_neg_iff_add_eq_zero.mpr hsum).trans
    (eq_neg_iff_add_eq_zero.mpr (solution A h (y * x))).symm

#print axioms solution
#print axioms multiplication_commutes
