-- Prove2me | solution 1 for ErdosProblems.Erdos243.LcmRecordCrossing.finite_record_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:55:53.896742+00:00
-- url     : https://prove2.me/submissions/ea678bb0-e065-4b4e-94d9-8b6a15756da5

import Mathlib
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_crossed_progression_card_le_excess
import Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_sum_firstCrossing_partition
open ErdosProblems.Erdos243 ErdosProblems.Erdos243.LcmRecordCrossing

private theorem crossed_progression_weighted_charge (s : Finset ℕ)
    (x P U d B : ℕ) (a L : ℤ) (hP : B < P)
    (hlo : ∀ k ∈ s, U < x + k * P)
    (hhi : ∀ k ∈ s, x + k * P ≤ U + d)
    (hfeedback : (d : ℤ) = (a - 1) * U - L)
    (hcover : ∀ k ∈ s, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : 0 ≤ f U) :
    ∑ k ∈ s, f (x + k * P) ≤ ((d - B : ℕ) : ℝ) * f U := by
  have hc := crossed_progression_card_le_excess s x P U d B a L hP hlo hhi
    hfeedback hcover
  calc
    ∑ k ∈ s, f (x + k * P) ≤ ∑ _k ∈ s, f U :=
      Finset.sum_le_sum (fun k hk => hf (Nat.le_of_lt (hlo k hk)))
    _ = (s.card : ℝ) * f U := by simp
    _ ≤ ((d - B : ℕ) : ℝ) * f U :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hpos

theorem solution (s : Finset ℕ) (U : ℕ → ℕ)
    (a L : ℕ → ℤ) (x P B N : ℕ) (hP : B < P)
    (hzero : ∀ k ∈ s, U 0 < x + k * P)
    (hN : ∀ k ∈ s, ∃ j ≤ N, x + k * P ≤ U j)
    (hfeedback : ∀ n < N, (∀ j ≤ n, U j < U (n + 1)) →
      ((U (n + 1) - U n : ℕ) : ℤ) = (a n - 1) * U n - L n)
    (hcover : ∀ n < N, ∀ k ∈ s, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L n ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u) :
    ∑ k ∈ s, f (x + k * P) ≤
      ∑ n ∈ Finset.range N,
        if (∀ j ≤ n, U j < U (n + 1)) then
          ((U (n + 1) - U n - B : ℕ) : ℝ) * f (U n) else 0 := by
  classical
  rw [sum_firstCrossing_partition s U (fun k => x + k * P) N
    (fun k => f (x + k * P)) hzero hN]
  apply Finset.sum_le_sum
  intro n hn
  have hnN := Finset.mem_range.mp hn
  by_cases hr : ∀ j ≤ n, U j < U (n + 1)
  · rw [if_pos hr]
    let crossed := s.filter (fun k => FirstCrossing U (x + k * P) n)
    have hlocal := crossed_progression_weighted_charge crossed x P (U n)
      (U (n + 1) - U n) B (a n) (L n) hP
      (by
        intro k hk
        have hcross := (Finset.mem_filter.mp hk).2
        exact hcross.1 n (Nat.le_refl n))
      (by
        intro k hk
        have hcross := (Finset.mem_filter.mp hk).2.2
        have hrise := hr n (Nat.le_refl n)
        omega)
      (hfeedback n hnN hr)
      (by
        intro k hk
        exact hcover n hnN k (Finset.mem_filter.mp hk).1)
      f hf (hpos (U n))
    simpa only [crossed, Finset.sum_filter] using hlocal
  · rw [if_neg hr]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k hk
    exact if_neg (fun h => hr (fun j hj => (h.1 j hj).trans_le h.2))
