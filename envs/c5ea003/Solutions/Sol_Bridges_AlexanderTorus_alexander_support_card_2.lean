-- Prove2me | solution 2 for Bridges.AlexanderTorus.alexander_support_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:18:41.138048+00:00
-- url     : https://prove2.me/submissions/a0915463-e182-4fcd-ba33-cca240370f33

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
open Bridges.AlexanderTorus Polynomial Finset in
theorem solution (N : ℕ) : (alexander N).support.card = N := by
  have hC : ∀ i : ℕ, ((-1 : Polynomial ℤ) ^ i) = Polynomial.C ((-1 : ℤ) ^ i) := by
    intro i
    simp [Polynomial.C_pow]
  have halex : alexander N
      = ∑ i ∈ Finset.range N, Polynomial.C ((-1 : ℤ) ^ i) * (Polynomial.X : Polynomial ℤ) ^ i := by
    unfold alexander
    exact Finset.sum_congr rfl (fun i _ => by rw [hC i])
  have hcoeff : ∀ j : ℕ, (alexander N).coeff j = if j < N then (-1 : ℤ) ^ j else 0 := by
    intro j
    rw [halex, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (Finset.range N) j (fun i => (-1 : ℤ) ^ i)]
    simp [Finset.mem_range]
  have hsupp : (alexander N).support = Finset.range N := by
    ext j
    simp only [Polynomial.mem_support_iff, hcoeff, Finset.mem_range]
    by_cases hj : j < N
    · simp [hj]
    · simp [hj]
  rw [hsupp, Finset.card_range]
