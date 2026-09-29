-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.multiplier_one_tail_descent
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:16:43.386412+00:00
-- url     : https://prove2.me/submissions/eab1929c-8997-4704-a984-ca5bacbf7630

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
    (a u v : ℕ → ℕ) (T : ℕ)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (ha : ∀ n, T ≤ n → a n = 1) :
    ∀ k : ℕ, u (T + k) + k * v T = u T ∧ v (T + k) = v T := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : u (T + k + 1) + v T = u (T + k) := by
        simpa only [ha (T + k) (by omega), one_mul, ih.2] using
          hnum (T + k) (by omega)
      constructor
      · calc
          u (T + (k + 1)) + (k + 1) * v T =
              (u (T + k + 1) + v T) + k * v T := by
                rw [show T + (k + 1) = T + k + 1 by omega]
                ring
          _ = u (T + k) + k * v T := by rw [hstep]
          _ = u T := ih.1
      · rw [show T + (k + 1) = T + k + 1 by omega,
          hden (T + k) (by omega), ha (T + k) (by omega), one_mul, ih.2]
