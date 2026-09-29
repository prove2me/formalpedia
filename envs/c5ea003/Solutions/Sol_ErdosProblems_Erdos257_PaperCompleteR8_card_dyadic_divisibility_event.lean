-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.card_dyadic_divisibility_event
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:31:14.5927+00:00
-- url     : https://prove2.me/submissions/744b100a-634d-446c-b89f-bd330f3b6ebe

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Theorems.Thm_ErdosProblems_Erdos257_card_Icc_one_filter_dvd
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
theorem solution (d X : ℕ) (hd : 0 < d) :
    ((Icc 1 X).filter (fun n => d ∣ n ∧ ¬ 2 * d ∣ n)).card =
      X / d - X / (2 * d) := by
  have hsub : (Icc 1 X).filter (fun n => 2 * d ∣ n) ⊆
      (Icc 1 X).filter (fun n => d ∣ n) := by
    intro n hn
    obtain ⟨hnX, hn⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnX, (dvd_mul_left d 2).trans hn⟩
  have heq : (Icc 1 X).filter (fun n => d ∣ n ∧ ¬ 2 * d ∣ n) =
      (Icc 1 X).filter (fun n => d ∣ n) \
        (Icc 1 X).filter (fun n => 2 * d ∣ n) := by
    ext n
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [heq, card_sdiff_of_subset hsub, card_Icc_one_filter_dvd hd,
    card_Icc_one_filter_dvd (by omega)]
