-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:50:15.914624+00:00
-- url     : https://prove2.me/submissions/baa4d263-0671-43b9-94a0-417b9aafaf28

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
open Bridges.AlexanderTorus Polynomial in
theorem solution {N : ℕ} (hN : Odd N) : (alexander N).natDegree = N - 1 := by
  have hN1 : 1 ≤ N := hN.pos
  -- the coefficientwise description (the `alexander_coeff` argument, inlined)
  have hcoeff : ∀ i : ℕ, (alexander N).coeff i = if i < N then (-1 : ℤ) ^ i else 0 := by
    intro i
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
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [hcoeff m, if_neg (by omega)]
  · rw [hcoeff (N - 1), if_pos (by omega)]
    exact pow_ne_zero _ (by norm_num)
