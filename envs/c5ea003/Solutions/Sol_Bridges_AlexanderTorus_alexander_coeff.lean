-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:37:47.449979+00:00
-- url     : https://prove2.me/submissions/50ab4bc2-379b-4fcd-a4f9-799e4ddb79df

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
open Bridges.AlexanderTorus Polynomial in
theorem solution (N i : ℕ) :
    (alexander N).coeff i = if i < N then (-1 : ℤ) ^ i else 0 := by
  have hC : ∀ j : ℕ, ((-1 : Polynomial ℤ)) ^ j * Polynomial.X ^ j
      = Polynomial.monomial j ((-1 : ℤ) ^ j) := by
    intro j
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_pow]
    congr 2
    simp
  rw [alexander, Polynomial.finsetSum_coeff]
  simp only [hC, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range N) i (fun j => (-1 : ℤ) ^ j)]
  simp
