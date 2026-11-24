-- Prove2me | solution 1 for SingularModuli.successCount_H15_221
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:52:23.037666+00:00
-- url     : https://prove2.me/submissions/68ff4be8-4658-40b1-a0fc-ee4981c3b10c

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_Experiments
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier


namespace SingularModuli

open Polynomial Finset FactoringBarriers

theorem solution : successCount H15 221 = 17 := by
  letI hdec : DecidablePred (NontrivialDivisor 221) := fun d => by
    unfold NontrivialDivisor
    infer_instance
  have hconv : ∀ j : ℤ, evalGcd H15 j 221 = Nat.gcd (j ^ 2 + 191025 * j - 121287375).natAbs 221 := by
    intro j
    rw [evalGcd, Int.gcd_def, Int.natAbs_natCast]
    congr 1
    simp only [H15, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  have hb : ∀ k ∈ ({5, 18, 31, 44, 57, 70, 83, 96, 109, 122, 135, 148, 161, 174, 187, 200, 213} : Finset ℕ), k < 221 := by
    decide
  have hmem : ∀ j : ℕ, j ∈ successSet H15 221 ↔
      j ∈ ({5, 18, 31, 44, 57, 70, 83, 96, 109, 122, 135, 148, 161, 174, 187, 200, 213} : Finset ℕ) := by
    intro j
    simp only [successSet, Finset.mem_filter, Finset.mem_range]
    rw [hconv (j : ℤ)]
    by_cases hj : j < 221
    · simp only [hj, true_and]
      interval_cases j <;> decide
    · have hL : j ∉ ({5, 18, 31, 44, 57, 70, 83, 96, 109, 122, 135, 148, 161, 174, 187, 200, 213} : Finset ℕ) :=
        fun hmem => absurd (hb j hmem) (by omega)
      simp [hj, hL]
  have hset : successSet H15 221 = ({5, 18, 31, 44, 57, 70, 83, 96, 109, 122, 135, 148, 161, 174, 187, 200, 213} : Finset ℕ) :=
    Finset.ext hmem
  rw [successCount, hset]
  decide

end SingularModuli

open SingularModuli

theorem solution : successCount H15 221 = 17 :=
  SingularModuli.solution

#print axioms solution
