-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellMat_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T20:05:30.34481+00:00
-- url     : https://prove2.me/submissions/c998f45e-762c-4b89-9705-1bff68049b5f

import Mathlib
import Definitions.Def_Novelty_PellSpineCore
open Catalog.Novelty.PellSpine Finset in
theorem solution (n : ℕ) :
    pellMat ^ (n + 1) = !![(pellP (n + 2) : ℤ), (pellP (n + 1) : ℤ);
                            (pellP (n + 1) : ℤ), (pellP n : ℤ)] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pellMat, pellP]
  | succ n ih =>
    rw [pow_succ, ih, show n + 1 + 1 = n + 2 from rfl]
    have e2 : ((pellP (n + 1 + 2) : ℕ) : ℤ) = 2 * (pellP (n + 2) : ℤ) + (pellP (n + 1) : ℤ) := by
      rw [show pellP (n + 1 + 2) = 2 * pellP (n + 2) + pellP (n + 1) from rfl]
      push_cast
      ring
    have e3 : ((pellP (n + 2) : ℕ) : ℤ) = 2 * (pellP (n + 1) : ℤ) + (pellP n : ℤ) := by
      rw [show pellP (n + 2) = 2 * pellP (n + 1) + pellP n from rfl]
      push_cast
      ring
    generalize ((pellP (n + 1 + 2) : ℕ) : ℤ) = A at e2 e3 ⊢
    generalize ((pellP (n + 2) : ℕ) : ℤ) = B at e2 e3 ⊢
    generalize ((pellP (n + 1) : ℕ) : ℤ) = C at e2 e3 ⊢
    generalize ((pellP n : ℕ) : ℤ) = D at e2 e3 ⊢
    subst e2
    subst e3
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pellMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
