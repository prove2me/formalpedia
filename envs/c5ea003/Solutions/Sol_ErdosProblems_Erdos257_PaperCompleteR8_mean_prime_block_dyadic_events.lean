-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.mean_prime_block_dyadic_events
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:07:24.687913+00:00
-- url     : https://prove2.me/submissions/00058f2b-3ab4-4cf7-bca3-066072124dad

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_mean_dyadic_divisibility_event
import Mathlib

namespace ErdosProblems.Erdos257.PaperCompleteR8
end ErdosProblems.Erdos257.PaperCompleteR8

/-! # Exact finite-period counts for dyadic logarithmic events

For the separating divisor frames, the event for a prime in row k is
2^(k+2)*p divides n but 2^(k+3)*p does not. Counting it by subtraction
avoids probabilistic independence assumptions or limiting density suppliers.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (P : Finset ℕ) (r X : ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hX : 0 < X)
    (hperiod : ∀ p ∈ P, 2 * (2 ^ r * p) ∣ X) :
    (∑ n ∈ Icc 1 X, ∑ p ∈ P,
      if 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n then (1 : ℝ) else 0) /
        (X : ℝ) =
      (∑ p ∈ P, (1 : ℝ) / p) / (2 * (2 : ℝ) ^ r) := by
  classical
  rw [sum_comm, sum_div, sum_div]
  apply sum_congr rfl
  intro p hp
  rw [mean_dyadic_divisibility_event _ X
    (Nat.mul_pos (Nat.pow_pos (by decide)) (hP p hp)) hX (hperiod p hp)]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
