-- Prove2me | solution 1 for BookSixth.permanent_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T00:29:20.615009+00:00
-- url     : https://prove2.me/submissions/8c7e0072-0361-4a6f-8828-1dd9f4544b67

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (hn : 0 < n) :
    Matrix.permanent (fun (_ : Fin n) (_ : Fin n) => ((n : ℝ))⁻¹) = (n.factorial : ℝ) / (n : ℝ) ^ n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Matrix.permanent]
  simp only [Finset.prod_const, Fintype.card_fin]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [div_eq_mul_inv, inv_pow, Finset.card_univ, Fintype.card_fin]
