-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperCoverageV5_depth_four_minimum
-- name    : ErdosProblems.Erdos68.PaperCoverageV5.depth_four_minimum
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:17:47.585745+00:00
-- url     : https://prove2.me/theorems/d42c0fe3-1cdb-4ff7-992f-a7e3172a6524
-- title:
--   Least positive depth-four channel moment
-- statement:
--   The moment 1380 is attained by an admissible finitely supported integer vector with channels 2, 3, and 4 zero; every positive moment attained under those same conditions is at least 1380.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCoverageV5/MomentExamples.lean#L156-L163
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

theorem ErdosProblems.Erdos68.PaperCoverageV5.depth_four_minimum : AttainsMoment 4 1380 ∧
    ∀ m : ℤ, AttainsMoment 4 m → 0 < m → 1380 ≤ m := by sorry
