-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_mod_seven_quartic_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:13:10.886763+00:00
-- url     : https://prove2.me/submissions/73a23026-2bbe-4cb5-8a87-1b5eeb8149a9

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticCertificates
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_quartic_ratio_density
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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
import Mathlib.Tactic
import Mathlib.Tactic.Ring

attribute [local instance] ErdosProblems.Erdos243.PaperCompleteR11.instFactPrimeOfNatNat_erdosProblems_1
   
                                           

                                                                            
                                                                          
                                                                             
                                                                        
  

namespace ErdosProblems.Erdos243.PaperCompleteR11
/-- All listed ratio classes have an explicit obstructed root modulo 7. -/
theorem mod_seven_quartic_witness (ρ : ZMod 7)
    (hρ : ρ = 1 ∨ ρ = 3 ∨ ρ = 4 ∨ ρ = 6) : CubicQuarticWitness 7 ρ := by
  rcases hρ with rfl | rfl | rfl | rfl
  · exact ⟨5, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨3, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨4, by decide, by unfold CubicQuarticNonresidue; decide⟩
  · exact ⟨2, by decide, by unfold CubicQuarticNonresidue; decide⟩
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 7) ≠ 0)
    (hρ : (c : ZMod 7) / (m : ZMod 7) = 1 ∨
      (c : ZMod 7) / (m : ZMod 7) = 3 ∨
      (c : ZMod 7) / (m : ZMod 7) = 4 ∨
      (c : ZMod 7) / (m : ZMod 7) = 6) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 7) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact integral_cubic_quartic_ratio_density a u v m c T 7 (by decide)
    hnum hden hm (mod_seven_quartic_witness _ hρ)
