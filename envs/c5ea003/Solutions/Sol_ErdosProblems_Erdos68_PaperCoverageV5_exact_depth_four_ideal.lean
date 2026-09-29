-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperCoverageV5.exact_depth_four_ideal
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:41:40.598984+00:00
-- url     : https://prove2.me/submissions/6a41d9a5-c283-454d-afc3-c6e28b6d72d0

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
import Definitions.Def_ErdosProblems_Erdos68_PaperCoverageV5_MomentExamples
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_odd
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_recurrence
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_channelScalar_two
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_attainable_moment_ideal
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

theorem scalar_9 : channelScalar 9 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_10 : channelScalar 10 = -226800 := by
  rw [channelScalar_recurrence (by decide : 2 < 10)]
  rw [show Finset.Ico 2 10 = ({2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9]

theorem scalar_11 : channelScalar 11 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_12 : channelScalar 12 = -14386680 := by
  rw [channelScalar_recurrence (by decide : 2 < 12)]
  rw [show Finset.Ico 2 12 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11]

theorem scalar_13 : channelScalar 13 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_14 : channelScalar 14 = -1362160800 := by
  rw [channelScalar_recurrence (by decide : 2 < 14)]
  rw [show Finset.Ico 2 14 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13]

theorem scalar_15 : channelScalar 15 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_16 : channelScalar 16 = -162648486000 := by
  rw [channelScalar_recurrence (by decide : 2 < 16)]
  rw [show Finset.Ico 2 16 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13, scalar_14, scalar_15]

theorem scalar_17 : channelScalar 17 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_18 : channelScalar 18 = -25006184723520 := by
  rw [channelScalar_recurrence (by decide : 2 < 18)]
  rw [show Finset.Ico 2 18 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13, scalar_14, scalar_15, scalar_16, scalar_17]

theorem scalar_19 : channelScalar 19 = 0 := by
  exact channelScalar_odd (by decide) (by decide)

theorem scalar_20 : channelScalar 20 = -4748053349239200 := by
  rw [channelScalar_recurrence (by decide : 2 < 20)]
  rw [show Finset.Ico 2 20 = ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} : Finset ℕ) from by decide]
  norm_num [channelWeight, channelScalar_two, scalar_3, scalar_4, scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13, scalar_14, scalar_15, scalar_16, scalar_17, scalar_18, scalar_19]

theorem finite_scalar_gcd_four : finiteScalarGcd 4 20 = 60 := by
  unfold finiteScalarGcd
  rw [show Finset.Icc (4 + 1) 20 = ({5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20} : Finset ℕ) from by decide]
  norm_num [scalar_5, scalar_6, scalar_7, scalar_8, scalar_9, scalar_10, scalar_11, scalar_12, scalar_13, scalar_14, scalar_15, scalar_16, scalar_17, scalar_18, scalar_19, scalar_20]
  decide +kernel



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

theorem minimumMoment_four : minimumMoment 4 3 = 1380 := by
  norm_num [minimumMoment, finite_scalar_gcd_four, kernelOne_four, lcm_four_value]
end ErdosProblems.Erdos68.PaperCoverageV5

open ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperCoverageV5 in
theorem solution (m : ℤ) : AttainsMoment 4 m ↔ (1380 : ℤ) ∣ m := by
  simpa only [minimumMoment_four] using
    attainable_moment_ideal (D := 4) (p := 3)
      (by decide) (by decide) (by decide) (by decide) m
