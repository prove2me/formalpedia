-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.earlier_multiplier_dvd_later_denominator
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:51:05.985347+00:00
-- url     : https://prove2.me/submissions/17735f5b-1dbb-4d8d-b343-92cffd44e9e5

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
    (a v : ℕ → ℕ) (T : ℕ)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (i j : ℕ) (hi : T ≤ i) (hij : i < j) : a i ∣ v j := by
  have h : ∀ k : ℕ, a i ∣ v (i + 1 + k) := by
    intro k
    induction k with
    | zero =>
        simp only [Nat.add_zero]
        rw [hden i hi]
        exact dvd_mul_right _ _
    | succ k ih =>
        rw [show i + 1 + (k + 1) = (i + 1 + k) + 1 by omega,
          hden (i + 1 + k) (by omega)]
        exact dvd_mul_of_dvd_right ih _
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ j by omega)
  simpa only [← hk] using h k
