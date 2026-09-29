-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.primitive_zero_density_multiplier_irreducibility
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:39:32.094172+00:00
-- url     : https://prove2.me/submissions/4731bb37-1a78-440d-846f-5b053e8f9ed0

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_ZeroLowerDensity_not_positive_lower_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_earlier_multiplier_dvd_later_denominator
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_unit_irreducible_below_uniform
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_cubic_unit_constant_of_zero_lower_density
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_multiplier_arbitrarily_late_nonunit
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_multiplier_coprime_denominator
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_multiplier_prime_supply
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_step_adjacent_coprime
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
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c}) :
    (c = 1 ∨ c = -1) ∧
    (∀ n, T ≤ n → Nat.Coprime (a n) (v n)) ∧
    (∀ i j, T ≤ i → T ≤ j → i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ N, ∃ n, max T N ≤ n ∧ 1 < a n) ∧
    (∀ B N, ∃ p j : ℕ, Nat.Prime p ∧ B < p ∧ max T N ≤ j ∧ p ∣ a j) ∧
    Irreducible (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))) := by
  have hadj : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1)) := by
    intro n hn
    exact primitive_step_adjacent_coprime (a n) (u n) (v n) (u (n + 1))
      (hnum n hn) (hcop n hn)
  have hc := primitive_cubic_unit_constant_of_zero_lower_density u (m : ℤ) c T hadj hzero
  have hnumZ : ∀ n, T ≤ n → (u (n + 1) : ℤ) + (v n : ℤ) = (a n : ℤ) * (u n : ℤ) := by
    intro n hn
    exact_mod_cast hnum n hn
  have hdenZ : ∀ n, T ≤ n → (v (n + 1) : ℤ) = (a n : ℤ) * (v n : ℤ) := by
    intro n hn
    exact_mod_cast hden n hn
  refine ⟨hc, primitive_multiplier_coprime_denominator a u v T hnum hden hcop,
    primitive_multipliers_pairwise_coprime a u v T hnum hden hcop,
    primitive_multiplier_arbitrarily_late_nonunit a u v T hv hnum hden,
    primitive_multiplier_prime_supply a u v T hv hnum hden hcop, ?_⟩
  exact integral_cubic_unit_irreducible_below_uniform
    (fun n ↦ (a n : ℤ)) (fun n ↦ (u n : ℤ)) (fun n ↦ (v n : ℤ)) m c T hm hc
    hnumZ hdenZ (hzero.not_positive_lower_bound (1 / 28) (by norm_num))
