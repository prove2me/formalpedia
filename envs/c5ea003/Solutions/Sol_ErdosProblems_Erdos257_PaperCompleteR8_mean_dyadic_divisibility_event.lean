-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.mean_dyadic_divisibility_event
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:02:36.712203+00:00
-- url     : https://prove2.me/submissions/119be102-690f-4779-8fa5-5041a6c37731

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_card_dyadic_divisibility_event
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



/-- At a complete period, exactly half the multiples survive. -/
theorem card_dyadic_divisibility_event_period (d X : ℕ)
    (hd : 0 < d) (hperiod : 2 * d ∣ X) :
    ((Icc 1 X).filter (fun n => d ∣ n ∧ ¬ 2 * d ∣ n)).card =
      X / (2 * d) := by
  rw [card_dyadic_divisibility_event d X hd]
  obtain ⟨m, rfl⟩ := hperiod
  have hfirst : (2 * d * m) / d = 2 * m := by
    rw [show 2 * d * m = (2 * m) * d by ring]
    exact Nat.mul_div_cancel _ hd
  have hsecond : (2 * d * m) / (2 * d) = m := by
    rw [mul_comm (2 * d) m]
    exact Nat.mul_div_cancel _ (by omega)
  rw [hfirst, hsecond]
  omega
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (d X : ℕ) (hd : 0 < d)
    (hX : 0 < X) (hperiod : 2 * d ∣ X) :
    (∑ n ∈ Icc 1 X, if d ∣ n ∧ ¬ 2 * d ∣ n then (1 : ℝ) else 0) /
        (X : ℝ) = 1 / (2 * (d : ℝ)) := by
  classical
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  rw [card_dyadic_divisibility_event_period d X hd hperiod]
  have hden : (2 * d : ℕ) ≠ 0 := by omega
  rw [Nat.cast_div hperiod (by exact_mod_cast hden)]
  push_cast
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  field_simp
