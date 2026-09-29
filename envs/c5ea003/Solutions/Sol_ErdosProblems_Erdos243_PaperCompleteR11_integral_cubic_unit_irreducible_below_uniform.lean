-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_unit_irreducible_below_uniform
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:19:40.478831+00:00
-- url     : https://prove2.me/submissions/23b06a93-2492-40f7-b561-e9937678b080

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_LowerDensityAtLeast_mono_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_mod_five_density
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_unit_cubic_rational_root_scale
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_unit_cubic_irreducible_of_scale
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
/-- Both exceptional scales really have rational roots, for either sign. -/
theorem unit_cubic_exists_rational_root_iff
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1) :
    (∃ r : ℚ, (m : ℚ) * (r ^ 3 - r) + 6 * c = 0) ↔ m = 1 ∨ m = 16 := by
  constructor
  · rintro ⟨r, hr⟩
    exact unit_cubic_rational_root_scale m c r hm hc hr
  · intro hh
    rcases hh with rfl | rfl <;> rcases hc with rfl | rfl
    · exact ⟨-2, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨1 / 2, by norm_num⟩
    · exact ⟨-1 / 2, by norm_num⟩



/-- Entire rational-root unit branch, with a strictly stronger density bound
than 1/28 and with no global prime-existence hypothesis. -/
theorem integral_cubic_unit_rational_root_density
    (a u v : ℕ → ℤ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ℚ) (hroot : (m : ℚ) * (r ^ 3 - r) + 6 * (c : ℚ) = 0) :
    LowerDensityAtLeast {n : ℕ | u n ≠ (m : ℤ) * risingBinomial n + c} (1 / 5) := by
  have hcQ : (c : ℚ) = 1 ∨ (c : ℚ) = -1 := by
    rcases hc with rfl | rfl <;> norm_num
  have hmcase := unit_cubic_rational_root_scale m (c : ℚ) r hm hcQ hroot
  apply integral_cubic_mod_five_density a u v (m : ℤ) c T hnum hden
  · rcases hmcase with rfl | rfl <;> decide
  · rcases hmcase with rfl | rfl <;> rcases hc with rfl | rfl <;> decide
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a u v : ℕ → ℤ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | u n ≠ (m : ℤ) * risingBinomial n + c}
      (1 / 28)) :
    Irreducible (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))) := by
  have hnroot : ¬ ∃ r : ℚ, (m : ℚ) * (r ^ 3 - r) + 6 * (c : ℚ) = 0 := by
    rintro ⟨r, hr⟩
    exact hlow ((integral_cubic_unit_rational_root_density a u v m c T hm hc
      hnum hden r hr).mono_bound (by norm_num))
  have hcQ : (c : ℚ) = 1 ∨ (c : ℚ) = -1 := by
    rcases hc with rfl | rfl <;> norm_num
  have hcase : ¬ (m = 1 ∨ m = 16) :=
    fun hh ↦ hnroot ((unit_cubic_exists_rational_root_iff m (c : ℚ) hm hcQ).mpr hh)
  exact unit_cubic_irreducible_of_scale m (c : ℚ) hm hcQ
    (fun hh ↦ hcase (Or.inl hh)) (fun hh ↦ hcase (Or.inr hh))
