-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_irreducible_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:16:40.607353+00:00
-- url     : https://prove2.me/submissions/c9ceb976-6d0f-4c11-a36c-3f6e823f1359

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubicScalePolynomial_natDegree
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_unit_cubic_rational_root_scale
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
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (hm1 : m ≠ 1) (hm16 : m ≠ 16) :
    Irreducible (cubicScalePolynomial (6 * c / (m : ℚ))) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp only [cubicScalePolynomial_natDegree, Finset.mem_Icc]
    omega
  · intro r hr
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    have hroot : (m : ℚ) * (r ^ 3 - r) + 6 * c = 0 := by
      have hh : r ^ 3 - r + 6 * c / (m : ℚ) = 0 := by
        simpa [Polynomial.IsRoot.def, cubicScalePolynomial] using hr
      field_simp [hm0] at hh
      linear_combination hh
    exact (unit_cubic_rational_root_scale m c r hm hc hroot).elim hm1 hm16
