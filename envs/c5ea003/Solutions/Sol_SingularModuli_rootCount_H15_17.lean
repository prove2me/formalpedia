-- Prove2me | solution 1 for SingularModuli.rootCount_H15_17
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:47:37.156423+00:00
-- url     : https://prove2.me/submissions/b45e57f4-f131-4a53-bdc5-fe783bb452ef

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_Experiments
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier

namespace SingularModuli

open Polynomial Finset FactoringBarriers

theorem solution : rootCount H15 17 = 0 := by
  have hev : ∀ x : ZMod 17, (redMod H15 17).eval x = x ^ 2 + 13 * x + 9 := by
    intro x
    simp only [redMod, H15]
    rw [Polynomial.eval_map]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    have h1 : (Int.castRingHom (ZMod 17)) 191025 = 13 := by
      rw [show (Int.castRingHom (ZMod 17)) 191025 = ((191025 : ℤ) : ZMod 17) from rfl]
      decide
    have h2 : (Int.castRingHom (ZMod 17)) 121287375 = 8 := by
      rw [show (Int.castRingHom (ZMod 17)) 121287375 = ((121287375 : ℤ) : ZMod 17) from rfl]
      decide
    rw [h1, h2, sub_eq_add_neg]
    rw [show (-(8 : ZMod 17)) = 9 from by decide]
  have hno : ∀ x : ZMod 17, x ^ 2 + 13 * x + 9 ≠ 0 := by decide
  have hset : rootFinset H15 17 = (∅ : Finset (ZMod 17)) := by
    ext x
    rw [rootFinset, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [hev x]
    simp [hno x]
  rw [rootCount, hset]
  decide

end SingularModuli

open SingularModuli

theorem solution : rootCount H15 17 = 0 :=
  SingularModuli.solution

#print axioms solution
