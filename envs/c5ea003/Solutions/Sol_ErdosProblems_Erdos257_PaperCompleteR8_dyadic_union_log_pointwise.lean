-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadic_union_log_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:07:26.198715+00:00
-- url     : https://prove2.me/submissions/2566d16b-9167-4f0f-87d5-72cb0071fbb7

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorCubeIncidence
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadic_exponent_eq_of_odd_cofactors
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_log_nat_nonneg
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_odd_cofactor_of_dyadic_event
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_two_pow_cubePrimeRank_le_incidence
import Mathlib

   
                                                 

                                                                 
                                                                          
                                                                           
                                                                     
  
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset











/-- A containing finite support inherits the cube's first logarithmic moment. -/
theorem cube_log_incidence_lower (q : ℕ) (P F : Finset ℕ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hn : 0 < n) (hqn : q ∣ n)
    (hF : divisorCube q P ⊆ F) :
    Real.log 2 * (cubePrimeRank q P n : ℝ) ≤
      Real.log ((F.filter (fun a => a ∣ n)).card : ℝ) := by
  have hsub : (divisorCube q P).filter (fun a => a ∣ n) ⊆
      F.filter (fun a => a ∣ n) := by
    intro a ha
    exact mem_filter.mpr ⟨hF (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩
  have hnat := (two_pow_cubePrimeRank_le_incidence q P n hq hP hn hqn).trans
    (Finset.card_le_card hsub)
  have hreal : (2 : ℝ) ^ cubePrimeRank q P n ≤
      ((F.filter (fun a => a ∣ n)).card : ℝ) := by exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ cubePrimeRank q P n) hreal
  simpa only [Real.log_pow, mul_comm] using hlog







/-- Row events at different exact dyadic valuations cannot coexist. -/
theorem dyadic_event_row_unique (k l p q n : ℕ) (hp : ¬ 2 ∣ p) (hq : ¬ 2 ∣ q)
    (he : 2 ^ (k + 2) * p ∣ n ∧ ¬ 2 * (2 ^ (k + 2) * p) ∣ n)
    (hf : 2 ^ (l + 2) * q ∣ n ∧ ¬ 2 * (2 ^ (l + 2) * q) ∣ n) : k = l := by
  obtain ⟨u, hu, hnu⟩ := odd_cofactor_of_dyadic_event (k + 2) p n hp he
  obtain ⟨v, hv, hnv⟩ := odd_cofactor_of_dyadic_event (l + 2) q n hq hf
  have h := dyadic_exponent_eq_of_odd_cofactors hu hv (hnu.symm.trans hnv)
  omega
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (P : ℕ → Finset ℕ) (J : Finset ℕ) (n : ℕ)
    (hn : 0 < n) (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p) :
    Real.log 2 * (∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) ≤
      Real.log (((J.biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)).filter
        (fun a => a ∣ n)).card : ℝ) := by
  classical
  let F := J.biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)
  have hpodd : ∀ k p, p ∈ P k → ¬ 2 ∣ p := by
    intro k p hp hd
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hP k p hp).1).mp hd
    have hlt := (hP k p hp).2
    omega
  by_cases hex : ∃ k ∈ J, ∃ p ∈ P k,
      2 ^ (k + 2) * p ∣ n ∧ ¬ 2 * (2 ^ (k + 2) * p) ∣ n
  · obtain ⟨k, hk, p, hp, he⟩ := hex
    have hz : ∀ l ∈ J, l ≠ k → dyadicBlockCount (P l) (l + 2) n = 0 := by
      intro l hl hlk
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨hqP, hf⟩ := mem_filter.mp hq
      exact hlk (dyadic_event_row_unique l k q p n (hpodd l q hqP) (hpodd k p hp) hf he)
    have hsum : (∑ l ∈ J, (dyadicBlockCount (P l) (l + 2) n : ℝ)) =
        (dyadicBlockCount (P k) (k + 2) n : ℝ) := by
      apply Finset.sum_eq_single k
      · intro l hl hlk
        simp only [hz l hl hlk, Nat.cast_zero]
      · intro hnot
        exact False.elim (hnot hk)
    rw [hsum]
    have hcount : dyadicBlockCount (P k) (k + 2) n ≤
        cubePrimeRank (2 ^ (k + 2)) (P k) n := by
      apply Finset.card_le_card
      intro q hq
      exact mem_filter.mpr ⟨(mem_filter.mp hq).1, (mem_filter.mp hq).2.1⟩
    have hqn : 2 ^ (k + 2) ∣ n := (dvd_mul_right _ p).trans he.1
    have hF : divisorCube (2 ^ (k + 2)) (P k) ⊆ F := by
      intro a ha
      exact mem_biUnion.mpr ⟨k, hk, ha⟩
    have hlog := cube_log_incidence_lower (2 ^ (k + 2)) (P k) F n
      (Nat.pow_pos (by decide)) (fun p hp => (hP k p hp).1) hn hqn hF
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcount)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))).trans hlog
  · have hz : ∀ k ∈ J, dyadicBlockCount (P k) (k + 2) n = 0 := by
      intro k hk
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hex ⟨k, hk, p, (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
    have hs : (∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [hz k hk, Nat.cast_zero]
    rw [hs, mul_zero]
    exact log_nat_nonneg _
end
