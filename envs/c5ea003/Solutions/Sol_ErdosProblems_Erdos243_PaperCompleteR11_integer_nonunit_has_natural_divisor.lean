-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.integer_nonunit_has_natural_divisor
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:54:27.831911+00:00
-- url     : https://prove2.me/submissions/a2d752b0-1338-4d23-8cb8-98a292dd9c08

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
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
theorem solution (c : ℤ)
    (hc : c ≠ 1 ∧ c ≠ -1) :
    ∃ d : ℕ, 2 ≤ d ∧ (d : ℤ) ∣ c := by
  cases c with
  | ofNat n =>
      by_cases hn : n = 0
      · subst n
        exact ⟨2, by decide, dvd_zero _⟩
      · have hn1 : n ≠ 1 := by
          intro h
          subst n
          exact hc.1 rfl
        exact ⟨n, by omega, dvd_refl _⟩
  | negSucc n =>
      have hn : n ≠ 0 := by
        intro h
        subst n
        exact hc.2 rfl
      refine ⟨n + 1, by omega, -1, ?_⟩
      rw [Int.negSucc_eq]
      omega
