-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.natural_zero_lower_density_forces_modular_root_square
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:10:01.514159+00:00
-- url     : https://prove2.me/submissions/7d3be023-c025-40bb-9830-763a59795361

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_ZeroLowerDensity_not_positive_lower_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_single_prime_density
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

namespace ErdosProblems.Erdos243.PaperCompleteR20
end ErdosProblems.Erdos243.PaperCompleteR20

/-!
# Erdős 243: modular square data forced by zero exceptional density

This is the exact local input to the Chebotarev specialisation.  If the cubic
profile has zero lower density of exceptions, every good finite-field root of
the depressed cubic has square `r² - 1`; otherwise the already proved
single-prime obstruction gives positive lower density immediately.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR20
open ErdosProblems.Erdos243.PaperCompleteR11

/-- Zero lower density forces the square condition at each good modular root.
This packages the orbit-to-local direction without any prime-production or
number-field hypothesis. -/
theorem zero_lower_density_forces_modular_root_square
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hzero : ZeroLowerDensity {n : ℕ | u n ≠ m * risingBinomial n + c})
    (r : ZMod p)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hfactor : 3 * (m : ZMod p) * r ≠ 0) :
    IsSquare (r ^ 2 - 1) := by
  by_contra hns
  have hdensity := integral_cubic_single_prime_density
    a u v m c T p hp hnum hden r hroot hfactor hns
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  exact (hzero.not_positive_lower_bound (1 / (p : ℝ))
    (one_div_pos.mpr hpR)) hdensity
end ErdosProblems.Erdos243.PaperCompleteR20

open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (r : ZMod p)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hfactor : 3 * (m : ZMod p) * r ≠ 0) :
    IsSquare (r ^ 2 - 1) := by
  apply zero_lower_density_forces_modular_root_square
    (fun n ↦ (a n : ℤ)) (fun n ↦ (u n : ℤ)) (fun n ↦ (v n : ℤ))
    (m : ℤ) c T p hp
  · intro j hj
    exact_mod_cast hnum j hj
  · intro j hj
    exact_mod_cast hden j hj
  · exact hzero
  · simpa only [Int.cast_natCast] using hroot
  · simpa only [Int.cast_natCast] using hfactor
