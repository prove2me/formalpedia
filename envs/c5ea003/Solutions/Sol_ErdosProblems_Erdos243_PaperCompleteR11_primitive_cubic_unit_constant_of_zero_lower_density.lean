-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.primitive_cubic_unit_constant_of_zero_lower_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:33:39.016453+00:00
-- url     : https://prove2.me/submissions/81ecaab0-05f2-4868-a20d-bb663f7d3b03

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_ZeroLowerDensity_not_positive_lower_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integer_nonunit_has_natural_divisor
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_cubic_constant_divisor_density
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

/-!
# The complete zero-lower-density primitive-shape reduction

The manuscript's primitive-shape lemma is stated
under zero lower density, not under the universal positive threshold. Its
unit-constant conclusion is proved here at exactly that hypothesis.
The arbitrary positive-threshold theorem must not reuse that conclusion.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR9
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (u : ℕ → ℕ) (m c : ℤ) (T : ℕ)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1)))
    (hzero : ZeroLowerDensity {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}) :
    c = 1 ∨ c = -1 := by
  by_contra hc
  obtain ⟨d, hd, hdc⟩ := integer_nonunit_has_natural_divisor c (not_or.mp hc)
  have hlower := primitive_cubic_constant_divisor_density u m c T d hd hdc hcop
  exact (hzero.not_positive_lower_bound (1 / ((6 * d : ℕ) : ℝ))
    (by
      have hdpos : 0 < d := by omega
      positivity)) hlower
