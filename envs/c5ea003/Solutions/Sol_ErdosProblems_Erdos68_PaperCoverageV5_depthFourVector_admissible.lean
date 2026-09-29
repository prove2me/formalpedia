-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperCoverageV5.depthFourVector_admissible
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:24:21.399815+00:00
-- url     : https://prove2.me/submissions/3999aa4e-bad0-4b15-bcf1-edd9000efe43

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
import Definitions.Def_ErdosProblems_Erdos68_PaperCoverageV5_MomentExamples
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_admissible_iff
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_isolated_unit_outside
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_at_zero
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_odd
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_recurrence
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_two
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_expansion
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# Exact depth-four moment ideal and a supported attaining vector

The finite calculations below rewrite the actual isolated-unit recurrence;
they do not assume a table for an unrelated sequence.
The quadratic horizon (D,p,H)=(4,3,20) proves the infinite tail conclusion.
-/

namespace ErdosProblems.Erdos68.PaperCoverageV5
open ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp

theorem scalar_3 : channelScalar 3 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_4 : channelScalar 4 = -12 := by
  rw [channelScalar_recurrence (by decide : 2 < 4)]
  rw [show Finset.Ico 2 4 = ({2, 3} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3]

theorem scalar_5 : channelScalar 5 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_6 : channelScalar 6 = -180 := by
  rw [channelScalar_recurrence (by decide : 2 < 6)]
  rw [show Finset.Ico 2 6 = ({2, 3, 4, 5} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5]

theorem scalar_7 : channelScalar 7 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_8 : channelScalar 8 = -4200 := by
  rw [channelScalar_recurrence (by decide : 2 < 8)]
  rw [show Finset.Ico 2 8 = ({2, 3, 4, 5, 6, 7} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7]





























theorem kernelOne_scalar_formula (D : ℕ) :
    kernelOne D = (channelLCM D : ℤ) - ∑ d ∈ Finset.Icc 2 D,
      ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1)) * channelScalar d := by
  classical
  unfold kernelOne
  rw [canonicalKernel_expansion, Finsupp.sub_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_same, mul_one]
  rfl

theorem lcm_four_value : channelLCM 4 = 115 := by decide +kernel

theorem kernelOne_four : kernelOne 4 = -55 := by
  rw [kernelOne_scalar_formula]
  rw [show Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) from by decide]
  norm_num [lcm_four_value, channelScalar_two, scalar_3, scalar_4]
end ErdosProblems.Erdos68.PaperCoverageV5

open ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperCoverageV5 in
theorem solution : Admissible depthFourVector := by
  apply (admissible_iff _).mpr
  constructor
  · simp [depthFourVector, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
      canonicalKernel_at_zero, isolated_unit_outside 6 0 (Or.inl rfl),
      isolated_unit_outside 8 0 (Or.inl rfl)]
  · change 12 * kernelOne 4 + 253 * channelScalar 6 - 11 * channelScalar 8 = 0
    norm_num [kernelOne_four, scalar_6, scalar_8]
