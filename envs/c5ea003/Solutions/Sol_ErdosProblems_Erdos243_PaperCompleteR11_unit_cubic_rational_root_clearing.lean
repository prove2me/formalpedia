-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_rational_root_clearing
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:03:18.993115+00:00
-- url     : https://prove2.me/submissions/dc32c2a4-f0cd-471c-8209-01f89a4386d8

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_abs_reduced_positive
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
    (m : ℕ) (c r : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (hroot : (m : ℚ) * (r ^ 3 - r) + 6 * c = 0) :
    (r.num.natAbs < r.den ∧
      m * r.num.natAbs * (r.den ^ 2 - r.num.natAbs ^ 2) = 6 * r.den ^ 3) ∨
    (r.den < r.num.natAbs ∧
      m * r.num.natAbs * (r.num.natAbs ^ 2 - r.den ^ 2) = 6 * r.den ^ 3) := by
  have hr : r ≠ 0 := by
    intro hz
    rw [hz] at hroot
    rcases hc with rfl | rfl <;> norm_num at hroot
  obtain ⟨hs, ht, _, habs⟩ := rational_abs_reduced_positive r hr
  have hmR : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have htR : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast ht
  have ht0 : (r.den : ℚ) ≠ 0 := ne_of_gt htR
  have hcabs : |c| = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hfac : (m : ℚ) * r * (r ^ 2 - 1) = -6 * c := by
    linear_combination hroot
  have hA : (m : ℚ) * |r| * |(|r| ^ 2 - 1)| = 6 := by
    calc
      (m : ℚ) * |r| * |(|r| ^ 2 - 1)| = |(m : ℚ) * r * (r ^ 2 - 1)| := by
        rw [abs_mul, abs_mul, abs_of_pos hmR, sq_abs]
      _ = |-6 * c| := congrArg abs hfac
      _ = 6 := by rw [abs_mul, hcabs]; norm_num
  rw [habs] at hA
  have hne : r.num.natAbs ≠ r.den := by
    intro heq
    rw [heq, div_self ht0] at hA
    norm_num at hA
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · left
    refine ⟨hlt, ?_⟩
    have hpow : r.num.natAbs ^ 2 ≤ r.den ^ 2 := by nlinarith
    have hpowR : (r.num.natAbs : ℚ) ^ 2 ≤ (r.den : ℚ) ^ 2 := by exact_mod_cast hpow
    have hsq : ((r.num.natAbs : ℚ) / (r.den : ℚ)) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_iff₀ (sq_pos_of_pos htR)]
      simpa using hpowR
    have habsdiff : |((r.num.natAbs : ℚ) / (r.den : ℚ)) ^ 2 - 1| =
        ((r.den ^ 2 - r.num.natAbs ^ 2 : ℕ) : ℚ) / (r.den : ℚ) ^ 2 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hsq), Nat.cast_sub hpow]
      push_cast
      field_simp [ht0]
      <;> ring
    rw [habsdiff] at hA
    have hQ : (m : ℚ) * (r.num.natAbs : ℚ) *
        ((r.den ^ 2 - r.num.natAbs ^ 2 : ℕ) : ℚ) = 6 * (r.den : ℚ) ^ 3 := by
      field_simp [ht0] at hA
      nlinarith [hA]
    exact_mod_cast hQ
  · right
    refine ⟨hlt, ?_⟩
    have hpow : r.den ^ 2 ≤ r.num.natAbs ^ 2 := by nlinarith
    have hpowR : (r.den : ℚ) ^ 2 ≤ (r.num.natAbs : ℚ) ^ 2 := by exact_mod_cast hpow
    have hsq : 1 ≤ ((r.num.natAbs : ℚ) / (r.den : ℚ)) ^ 2 := by
      rw [div_pow, le_div_iff₀ (sq_pos_of_pos htR)]
      simpa using hpowR
    have habsdiff : |((r.num.natAbs : ℚ) / (r.den : ℚ)) ^ 2 - 1| =
        ((r.num.natAbs ^ 2 - r.den ^ 2 : ℕ) : ℚ) / (r.den : ℚ) ^ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsq), Nat.cast_sub hpow]
      push_cast
      field_simp [ht0]
      <;> ring
    rw [habsdiff] at hA
    have hQ : (m : ℚ) * (r.num.natAbs : ℚ) *
        ((r.num.natAbs ^ 2 - r.den ^ 2 : ℕ) : ℚ) = 6 * (r.den : ℚ) ^ 3 := by
      field_simp [ht0] at hA
      nlinarith [hA]
    exact_mod_cast hQ
