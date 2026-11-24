-- Prove2me | solution 1 for SingularModuli.successCount_H15_77
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:52:22.266549+00:00
-- url     : https://prove2.me/submissions/83d10c0a-2dcc-4ea4-ab5b-f9697f9fad1a

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_Experiments
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier


namespace SingularModuli

open Polynomial Finset FactoringBarriers

theorem solution : successCount H15 77 = 21 := by
  letI hdec : DecidablePred (NontrivialDivisor 77) := fun d => by
    unfold NontrivialDivisor
    infer_instance
  have hconv : ∀ j : ℤ, evalGcd H15 j 77 = Nat.gcd (j ^ 2 + 191025 * j - 121287375).natAbs 77 := by
    intro j
    rw [evalGcd, Int.gcd_def, Int.natAbs_natCast]
    congr 1
    simp only [H15, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  have hb : ∀ k ∈ ({0, 1, 6, 11, 12, 13, 20, 22, 23, 27, 33, 41, 44, 45, 48, 56, 62, 66, 67, 69, 76} : Finset ℕ), k < 77 := by
    decide
  have hmem : ∀ j : ℕ, j ∈ successSet H15 77 ↔
      j ∈ ({0, 1, 6, 11, 12, 13, 20, 22, 23, 27, 33, 41, 44, 45, 48, 56, 62, 66, 67, 69, 76} : Finset ℕ) := by
    intro j
    simp only [successSet, Finset.mem_filter, Finset.mem_range]
    rw [hconv (j : ℤ)]
    by_cases hj : j < 77
    · simp only [hj, true_and]
      interval_cases j <;> decide
    · have hL : j ∉ ({0, 1, 6, 11, 12, 13, 20, 22, 23, 27, 33, 41, 44, 45, 48, 56, 62, 66, 67, 69, 76} : Finset ℕ) :=
        fun hmem => absurd (hb j hmem) (by omega)
      simp [hj, hL]
  have hset : successSet H15 77 = ({0, 1, 6, 11, 12, 13, 20, 22, 23, 27, 33, 41, 44, 45, 48, 56, 62, 66, 67, 69, 76} : Finset ℕ) :=
    Finset.ext hmem
  rw [successCount, hset]
  decide

end SingularModuli

open SingularModuli

theorem solution : successCount H15 77 = 21 :=
  SingularModuli.solution

#print axioms solution
