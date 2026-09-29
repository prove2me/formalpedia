-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.zeroLowerDensity_iff_no_positive_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:30:13.979689+00:00
-- url     : https://prove2.me/submissions/a8e7d7be-1afd-422b-9db5-046d3a1de7f4

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_ZeroLowerDensity_not_positive_lower_bound
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
theorem solution (E : Set ℕ) :
    ZeroLowerDensity E ↔ ∀ d : ℝ, 0 < d → ¬ LowerDensityAtLeast E d := by
  constructor
  · exact fun h d hd ↦ h.not_positive_lower_bound d hd
  · intro h ε hε N
    by_contra hbad
    have hprefix : ∀ X : ℕ, N ≤ X → ε * (X : ℝ) ≤ (exceptionCount E X : ℝ) := by
      intro X hX
      apply le_of_not_gt
      intro hh
      exact hbad ⟨X, hX, hh⟩
    apply h ε hε
    intro δ hδ
    refine ⟨N, ?_⟩
    intro X hX
    have hh := hprefix X hX
    have hm := mul_nonneg (le_of_lt hδ) (show (0 : ℝ) ≤ (X : ℝ) by positivity)
    nlinarith
