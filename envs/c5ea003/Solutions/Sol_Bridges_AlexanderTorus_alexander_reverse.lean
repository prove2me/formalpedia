-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_reverse
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:54:31.355208+00:00
-- url     : https://prove2.me/submissions/0c1fd63f-1c50-4c03-8b25-0f397ac769c5

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
open Bridges.AlexanderTorus Polynomial Finset in
theorem solution {N : ℕ} (hN : Odd N) : (alexander N).reverse = alexander N := by
  have hN1 : 1 ≤ N := hN.pos
  have hev : Even (N - 1) := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by omega⟩
  -- coefficientwise description (the `alexander_coeff` argument, inlined)
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
  -- the degree (the `alexander_natDegree` argument, inlined)
  have hdeg : (alexander N).natDegree = N - 1 := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [hcoeff m, if_neg (by omega)]
    · rw [hcoeff (N - 1), if_pos (by omega)]
      exact pow_ne_zero _ (by norm_num)
  -- compare coefficients through `revAt`
  ext i
  rw [Polynomial.coeff_reverse, hdeg]
  by_cases hi : i ≤ N - 1
  · have hrev : Polynomial.revAt (N - 1) i = N - 1 - i := by
      rw [Polynomial.revAt_le hi]
    rw [hrev, hcoeff (N - 1 - i), hcoeff i, if_pos (by omega), if_pos (by omega)]
    -- `(-1)^(N-1-i) = (-1)^i` because `N-1` is even
    have hsum : (-1 : ℤ) ^ (N - 1 - i) * (-1 : ℤ) ^ i = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hi]
      exact hev.neg_one_pow
    have hsq : (-1 : ℤ) ^ i * (-1 : ℤ) ^ i = 1 := by
      rw [← pow_add, ← two_mul]
      exact (even_two_mul i).neg_one_pow
    calc (-1 : ℤ) ^ (N - 1 - i)
        = (-1 : ℤ) ^ (N - 1 - i) * ((-1 : ℤ) ^ i * (-1 : ℤ) ^ i) := by rw [hsq, mul_one]
      _ = ((-1 : ℤ) ^ (N - 1 - i) * (-1 : ℤ) ^ i) * (-1 : ℤ) ^ i := by ring
      _ = (-1 : ℤ) ^ i := by rw [hsum, one_mul]
  · have hrev : Polynomial.revAt (N - 1) i = i := by
      rw [Polynomial.revAt_eq_self_of_lt (by omega)]
    rw [hrev]
