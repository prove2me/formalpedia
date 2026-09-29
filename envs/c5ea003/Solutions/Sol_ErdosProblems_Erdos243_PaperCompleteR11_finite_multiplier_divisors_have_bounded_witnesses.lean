-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.finite_multiplier_divisors_have_bounded_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:51:07.333219+00:00
-- url     : https://prove2.me/submissions/1cb2b045-4328-4556-8f9a-ae8b5bfe8f68

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
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

   
                                      

                                                                  
                                                                              
                                                                            
                                                                          
  

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a : ℕ → ℕ) (T B : ℕ) :
    ∃ N : ℕ, ∀ p : ℕ, p ≤ B → (∃ i, T ≤ i ∧ p ∣ a i) →
      ∃ i, T ≤ i ∧ i ≤ N ∧ p ∣ a i := by
  classical
  induction B with
  | zero =>
      by_cases h : ∃ i, T ≤ i ∧ 0 ∣ a i
      · obtain ⟨i, hi, hd⟩ := h
        refine ⟨i, ?_⟩
        intro p hp _
        have hp0 : p = 0 := by omega
        subst p
        exact ⟨i, hi, le_refl i, hd⟩
      · refine ⟨0, ?_⟩
        intro p hp he
        have hp0 : p = 0 := by omega
        subst p
        exact False.elim (h he)
  | succ B ih =>
      obtain ⟨N, hN⟩ := ih
      by_cases h : ∃ i, T ≤ i ∧ (B + 1) ∣ a i
      · obtain ⟨i, hi, hd⟩ := h
        refine ⟨max N i, ?_⟩
        intro p hp he
        by_cases hpB : p ≤ B
        · obtain ⟨j, hj, hjN, hjd⟩ := hN p hpB he
          exact ⟨j, hj, le_trans hjN (le_max_left N i), hjd⟩
        · have hpeq : p = B + 1 := by omega
          subst p
          exact ⟨i, hi, le_max_right N i, hd⟩
      · refine ⟨N, ?_⟩
        intro p hp he
        by_cases hpB : p ≤ B
        · exact hN p hpB he
        · have hpeq : p = B + 1 := by omega
          subst p
          exact False.elim (h he)
