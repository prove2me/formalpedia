-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.primitive_multiplier_arbitrarily_late_nonunit
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:30:07.196593+00:00
-- url     : https://prove2.me/submissions/a861329d-6ff2-4780-ba4b-c686f04e4f3f

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_multiplier_one_tail_descent
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
/-- Positive next denominators force positive multipliers. -/
theorem primitive_multiplier_positive (a v : ℕ → ℕ) (T : ℕ)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n) :
    ∀ n, T ≤ n → 0 < a n := by
  intro n hn
  have hh := hv (n + 1) (by omega)
  rw [hden n hn] at hh
  by_contra h
  have hz : a n = 0 := by omega
  simp only [hz, zero_mul, lt_self_iff_false] at hh
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a u v : ℕ → ℕ) (T : ℕ)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (N : ℕ) : ∃ n, max T N ≤ n ∧ 1 < a n := by
  by_contra h
  push_neg at h
  let S := max T N
  have ha : ∀ n, S ≤ n → a n = 1 := by
    intro n hn
    have hnT : T ≤ n := le_trans (le_max_left T N) hn
    have hpos := primitive_multiplier_positive a v T hv hden n hnT
    have hle := h n hn
    omega
  have hnumS : ∀ n, S ≤ n → u (n + 1) + v n = a n * u n :=
    fun n hn ↦ hnum n (le_trans (le_max_left T N) hn)
  have hdenS : ∀ n, S ≤ n → v (n + 1) = a n * v n :=
    fun n hn ↦ hden n (le_trans (le_max_left T N) hn)
  have hh := (multiplier_one_tail_descent a u v S hnumS hdenS ha (u S + 1)).1
  have hvS : 1 ≤ v S := hv S (le_max_left T N)
  have hb := Nat.mul_le_mul_left (u S + 1) hvS
  nlinarith
