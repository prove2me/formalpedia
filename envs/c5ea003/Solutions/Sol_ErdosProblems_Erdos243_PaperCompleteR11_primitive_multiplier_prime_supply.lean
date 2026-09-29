-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.primitive_multiplier_prime_supply
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:33:40.315573+00:00
-- url     : https://prove2.me/submissions/b85718b9-d99b-4002-866a-dcf15d8a1449

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_earlier_multiplier_dvd_later_denominator
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_finite_multiplier_divisors_have_bounded_witnesses
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_multiplier_arbitrarily_late_nonunit
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_multiplier_coprime_denominator
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
import Mathlib.Tactic.Ring

   
                                      

                                                                  
                                                                              
                                                                            
                                                                          
  

namespace ErdosProblems.Erdos243.PaperCompleteR11
/-- Actual multipliers at distinct primitive-tail indices are coprime. -/
theorem primitive_multipliers_pairwise_coprime
    (a u v : ℕ → ℕ) (T : ℕ)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n)) :
    ∀ i j, T ≤ i → T ≤ j → i ≠ j → Nat.Coprime (a i) (a j) := by
  intro i j hi hj hne
  have hmult := primitive_multiplier_coprime_denominator a u v T hnum hden hcop
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ((hmult j hj).coprime_dvd_right
      (earlier_multiplier_dvd_later_denominator a v T hden i j hi hlt)).symm
  · exact (hmult i hi).coprime_dvd_right
      (earlier_multiplier_dvd_later_denominator a v T hden j i hj hlt)
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a u v : ℕ → ℕ) (T : ℕ)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (B N : ℕ) : ∃ p j : ℕ,
      Nat.Prime p ∧ B < p ∧ max T N ≤ j ∧ p ∣ a j := by
  obtain ⟨K, hK⟩ := finite_multiplier_divisors_have_bounded_witnesses a T B
  obtain ⟨j, hj, hunit⟩ := primitive_multiplier_arbitrarily_late_nonunit a u v T hv
    hnum hden (max N (K + 1))
  have hjT : T ≤ j := le_trans (le_max_left T _) hj
  have hjN : N ≤ j := by omega
  have hKj : K < j := by omega
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (show a j ≠ 1 by omega)
  have hpB : B < p := by
    by_contra h
    have hp_le : p ≤ B := by omega
    obtain ⟨i, hi, hiK, hpi⟩ := hK p hp_le ⟨j, hjT, hpa⟩
    have hij : i ≠ j := by omega
    have hc := primitive_multipliers_pairwise_coprime a u v T hnum hden hcop
      i j hi hjT hij
    have hp1 := Nat.eq_one_of_dvd_coprimes hc hpi hpa
    have hp2 := hp.two_le
    omega
  exact ⟨p, j, hp, hpB, max_le hjT hjN, hpa⟩
