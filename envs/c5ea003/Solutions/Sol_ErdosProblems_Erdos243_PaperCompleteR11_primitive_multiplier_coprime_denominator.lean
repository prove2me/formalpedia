-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.primitive_multiplier_coprime_denominator
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:30:09.228534+00:00
-- url     : https://prove2.me/submissions/aaff5486-dbcb-4ed9-8a2c-69b53a8c17ac

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
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n)) :
    ∀ n, T ≤ n → Nat.Coprime (a n) (v n) := by
  intro n hn
  let d := Nat.gcd (a n) (v n)
  have hda : d ∣ a n := Nat.gcd_dvd_left _ _
  have hdv : d ∣ v n := Nat.gcd_dvd_right _ _
  have hsum : d ∣ u (n + 1) + v n := by
    rw [hnum n hn]
    exact dvd_mul_of_dvd_left hda _
  have hdu : d ∣ u (n + 1) := (Nat.dvd_add_iff_left hdv).mpr hsum
  have hdv' : d ∣ v (n + 1) := by
    rw [hden n hn]
    exact dvd_mul_of_dvd_left hda _
  change d = 1
  exact Nat.eq_one_of_dvd_coprimes (hcop (n + 1) (by omega)) hdu hdv'
