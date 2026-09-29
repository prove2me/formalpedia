-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperCoverageV5.depthFourVector_moment
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:24:21.885283+00:00
-- url     : https://prove2.me/submissions/36d77f5d-5f2c-4d96-b65c-ed69fbaee3cc

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
import Definitions.Def_ErdosProblems_Erdos68_PaperCoverageV5_MomentExamples
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_smul
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_add
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_sub
import Theorems.Thm_ErdosProblems_Erdos68_factorialMoment_isolatedChannelUnit
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_moment
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











































theorem lcm_four_value : channelLCM 4 = 115 := by decide +kernel
end ErdosProblems.Erdos68.PaperCoverageV5

open ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperCoverageV5 in
theorem solution : factorialMoment depthFourVector = 1380 := by
  simp [depthFourVector, factorialMoment_add, factorialMoment_sub,
    factorialMoment_smul, canonicalKernel_moment, lcm_four_value,
    factorialMoment_isolatedChannelUnit (by decide : 2 ≤ 6),
    factorialMoment_isolatedChannelUnit (by decide : 2 ≤ 8)]
