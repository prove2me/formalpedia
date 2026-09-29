-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_natDegree_map_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:28:59.768993+00:00
-- url     : https://prove2.me/submissions/bb3adcf6-9d1c-48ef-9923-e5be13cf7b10

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXII
open Bridges.AlexanderTorus Polynomial in
theorem solution {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {N : ℕ} (hN : Odd N) :
    ((alexander N).map (Int.castRingHom (ZMod ℓ))).natDegree = N - 1 := by
  have hN1 : 1 ≤ N := hN.pos
  -- the reduction is `Σ_{i<N} (-1)^i X^i` over `ZMod ℓ`
  have hform : (alexander N).map (Int.castRingHom (ZMod ℓ))
      = ∑ i ∈ Finset.range N, C ((-1 : ZMod ℓ) ^ i) * X ^ i := by
    unfold alexander
    rw [Polynomial.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [hform]
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · -- every monomial has degree `< N`
    apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_X_pow_le _ _).trans (by simp at hi; omega)
  · -- the top coefficient is `(-1)^(N-1) ≠ 0`
    rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range N) (N - 1), if_pos (by simp; omega)]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
