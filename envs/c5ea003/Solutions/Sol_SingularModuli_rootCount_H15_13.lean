-- Prove2me | solution 1 for SingularModuli.rootCount_H15_13
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:47:37.663171+00:00
-- url     : https://prove2.me/submissions/539fe136-b477-4401-845b-1c21af54646f

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_Experiments
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier

namespace SingularModuli

open Polynomial Finset FactoringBarriers

theorem solution : rootCount H15 13 = 1 := by
  have hev : ∀ x : ZMod 13, (redMod H15 13).eval x = x ^ 2 + 3 * x + 12 := by
    intro x
    simp only [redMod, H15]
    rw [Polynomial.eval_map]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    have h1 : (Int.castRingHom (ZMod 13)) 191025 = 3 := by
      rw [show (Int.castRingHom (ZMod 13)) 191025 = ((191025 : ℤ) : ZMod 13) from rfl]
      decide
    have h2 : (Int.castRingHom (ZMod 13)) 121287375 = 1 := by
      rw [show (Int.castRingHom (ZMod 13)) 121287375 = ((121287375 : ℤ) : ZMod 13) from rfl]
      decide
    rw [h1, h2, sub_eq_add_neg]
    rw [show (-(1 : ZMod 13)) = 12 from by decide]
  have hroot : ∀ x : ZMod 13, x ^ 2 + 3 * x + 12 = 0 ↔ x = 5 := by decide
  have hset : rootFinset H15 13 = ({5} : Finset (ZMod 13)) := by
    ext x
    rw [rootFinset, Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and]
    rw [hev x]
    exact hroot x
  rw [rootCount, hset]
  decide

end SingularModuli

open SingularModuli

theorem solution : rootCount H15 13 = 1 :=
  SingularModuli.solution

#print axioms solution
