-- Prove2me | Definitions.Def_ErdosProblems_Erdos68_PaperCoverageV5_MomentExamples
-- name    : ErdosProblems_Erdos68_PaperCoverageV5_MomentExamples
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T16:02:38.781068+00:00
-- url     : https://prove2.me/theorems/d6c24869-b936-4292-9016-846faadc9718
-- title:
--   Explicit depth-four attaining-vector definition
-- statement:
--   Defines the explicit depth-four vector 12 • canonicalKernel 4 + 253 • isolatedChannelUnit 6 − 11 • isolatedChannelUnit 8. Its admissibility, channel cancellation, moment, content, and ideal are separate theorem nodes.
-- source:
--   Pinned Lean definition depthFourVector: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCoverageV5/MomentExamples.lean#L126-L128
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteDivisorCoordinates
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteIntegerSpan
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteLowKernel
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentIdeal
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



















































noncomputable def depthFourVector : ℕ →₀ ℤ :=
  (12 : ℤ) • canonicalKernel 4 + (253 : ℤ) • isolatedChannelUnit 6 -
    (11 : ℤ) • isolatedChannelUnit 8











end ErdosProblems.Erdos68.PaperCoverageV5


