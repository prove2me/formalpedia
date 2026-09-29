-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperCoverageV5.depthFourVector_channels
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:34:38.63828+00:00
-- url     : https://prove2.me/submissions/2c8f6db6-c4cf-4f33-86b0-0c1bac073706

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
import Definitions.Def_ErdosProblems_Erdos68_PaperCoverageV5_MomentExamples
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_smul
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_add
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_sub
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_isolatedChannelUnit
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_canonicalKernel_channel
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
end ErdosProblems.Erdos68.PaperCoverageV5

open ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperCoverageV5 in
theorem solution : LowChannels 4 depthFourVector := by
  intro d hd
  have hd2 := (Finset.mem_Icc.mp hd).1
  have hd4 := (Finset.mem_Icc.mp hd).2
  simp [depthFourVector, channelNumerator_add, channelNumerator_sub,
    channelNumerator_smul, canonicalKernel_channel hd2, hd4,
    channelNumerator_isolatedChannelUnit (by decide : 2 ≤ 6) hd2,
    channelNumerator_isolatedChannelUnit (by decide : 2 ≤ 8) hd2,
    show d ≠ 6 by omega, show d ≠ 8 by omega,
    show 6 ≠ d by omega, show 8 ≠ d by omega]
