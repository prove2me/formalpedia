-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_rational_root_scale
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:13:12.402974+00:00
-- url     : https://prove2.me/submissions/883404ba-4f5b-48bf-ae00-15a3212e89fe

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_abs_reduced_positive
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_unit_cubic_rational_root_clearing
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_unit_cubic_root_nat_classification
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
    (hroot : (m : ℚ) * (r ^ 3 - r) + 6 * c = 0) : m = 1 ∨ m = 16 := by
  have hr : r ≠ 0 := by
    intro hz
    rw [hz] at hroot
    rcases hc with rfl | rfl <;> norm_num at hroot
  obtain ⟨hs, ht, hcop, _⟩ := rational_abs_reduced_positive r hr
  have h := unit_cubic_root_nat_classification m r.num.natAbs r.den hs ht hcop
    (unit_cubic_rational_root_clearing m c r hm hc hroot)
  rcases h with ⟨_, _, hh⟩ | ⟨_, _, hh⟩
  · exact Or.inr hh
  · exact Or.inl hh
