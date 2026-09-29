-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperCoverageV5_depthFourVector_content_one
-- name    : ErdosProblems.Erdos68.PaperCoverageV5.depthFourVector_content_one
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:17:41.801353+00:00
-- url     : https://prove2.me/theorems/fc8423fc-8dbe-4361-ae79-93280e23d2f6
-- title:
--   Coefficient content one of the explicit vector
-- statement:
--   The gcd of the absolute values of the nonzero coefficients of the explicit vector 12 K₄ + 253 U₆ − 11 U₈ equals 1.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCoverageV5/MomentExamples.lean#L165-L177
--   Correspondence: finite channel-moment ideal in the Erdős #68 research record; no novelty or parent-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
import Definitions.Def_ErdosProblems_Erdos68_PaperCoverageV5_MomentExamples
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
open ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp

open ErdosProblems.Erdos68.PaperCoverageV5

theorem ErdosProblems.Erdos68.PaperCoverageV5.depthFourVector_content_one : coefficientContent depthFourVector = 1 := by sorry
