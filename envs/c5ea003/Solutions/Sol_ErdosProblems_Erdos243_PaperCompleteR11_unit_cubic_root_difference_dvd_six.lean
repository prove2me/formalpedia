-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_root_difference_dvd_six
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:11:33.434762+00:00
-- url     : https://prove2.me/submissions/a398f022-31e6-4b06-b862-8a0ce7732fbf

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
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
    (m s t : ℕ) (hcop : Nat.Coprime s t)
    (heq : (s < t ∧ m * s * (t ^ 2 - s ^ 2) = 6 * t ^ 3) ∨
      (t < s ∧ m * s * (s ^ 2 - t ^ 2) = 6 * t ^ 3)) :
    (s < t ∧ s * (t ^ 2 - s ^ 2) ∣ 6) ∨
      (t < s ∧ s * (s ^ 2 - t ^ 2) ∣ 6) := by
  have hpow : Nat.Coprime (s ^ 2) (t ^ 2) := (hcop.pow_left 2).pow_right 2
  have ht : t ∣ t ^ 2 := ⟨t, by ring⟩
  rcases heq with ⟨hlt, heq⟩ | ⟨hlt, heq⟩
  · left
    refine ⟨hlt, ?_⟩
    have hle : s ^ 2 ≤ t ^ 2 := by nlinarith
    have hd : Nat.Coprime (t ^ 2 - s ^ 2) (t ^ 2) :=
      (Nat.coprime_self_sub_left hle).mpr hpow
    have hc : Nat.Coprime (s * (t ^ 2 - s ^ 2)) (t ^ 3) :=
      (Nat.coprime_mul_iff_left.mpr ⟨hcop, hd.coprime_dvd_right ht⟩).pow_right 3
    apply hc.dvd_of_dvd_mul_right
    refine ⟨m, ?_⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using heq.symm
  · right
    refine ⟨hlt, ?_⟩
    have hle : t ^ 2 ≤ s ^ 2 := by nlinarith
    have hd : Nat.Coprime (s ^ 2 - t ^ 2) (t ^ 2) :=
      (Nat.coprime_sub_self_left hle).mpr hpow
    have hc : Nat.Coprime (s * (s ^ 2 - t ^ 2)) (t ^ 3) :=
      (Nat.coprime_mul_iff_left.mpr ⟨hcop, hd.coprime_dvd_right ht⟩).pow_right 3
    apply hc.dvd_of_dvd_mul_right
    refine ⟨m, ?_⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using heq.symm
