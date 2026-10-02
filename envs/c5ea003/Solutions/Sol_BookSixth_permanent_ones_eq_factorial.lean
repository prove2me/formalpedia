-- Prove2me | solution 1 for BookSixth.permanent_ones_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T07:59:35.932299+00:00
-- url     : https://prove2.me/submissions/8933741e-0bd1-40ca-b5a8-6afab34333e7

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : Nat) :
    Matrix.permanent (fun (_ : Fin n) (_ : Fin n) => (1 : Real))
      = (n.factorial : Real) := by
  rw [Matrix.permanent]
  simp only [Finset.prod_const_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
