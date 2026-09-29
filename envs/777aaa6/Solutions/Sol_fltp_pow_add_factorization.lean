-- Prove2me | solution 1 for fltp_pow_add_factorization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T10:37:12.805085+00:00
-- url     : https://prove2.me/submissions/ffc0be1b-e51b-4635-9469-6533b103e1d4

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem solution (p : ℕ) (h_odd : Odd p) (a b : ℤ) :
    a ^ p + b ^ p = (a + b) * ∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i) := by
  have key := (Commute.all a (-b : ℤ)).mul_geom_sum₂ p
  rw [sub_neg_eq_add] at key
  rw [h_odd.neg_pow, sub_neg_eq_add] at key
  exact key.symm
