-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_RecordDivisibility_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_RecordDivisibility_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:43:44.454573+00:00
-- url     : https://prove2.me/theorems/48a82b21-1639-4bed-bb14-97498cb21ecb
-- title:
--   Attainment of running maxima
-- statement:
--   Contains the source proof that every finite running maximum is attained at an index in its prefix. It is a supporting theorem bundle, not a new Definition of a mathematical object.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/RecordDivisibility.lean#L1-L159
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_RecordDivisibility_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.RecordDivisibility.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_GlobalLcmHeight
import Definitions.Def_ErdosProblems_Erdos243_CumulativeLcmTransfer
import Definitions.Def_ErdosProblems_Erdos243_LcmCriticalBoundary
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PrimitiveRecordBarrier
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Record fences without primitivity


Unlike a source-jump fence, the result below charges the *record increment*.
It allows arbitrarily deep intervening drawdowns and does not assume that
numerator and denominator are coprime. It is a finite ingredient of the
inclusive log-log argument, not a declaration of that analytic endpoint.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators

/-- The running maximum is an attained value, including at index zero. -/
theorem runningMax_attained (U : ℕ → ℕ) (n : ℕ) :
    ∃ j, j ≤ n ∧ U j = runningMax U n := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      obtain ⟨j, hj, heq⟩ := ih
      by_cases h : U (n + 1) ≤ runningMax U n
      · refine ⟨j, by omega, ?_⟩
        simpa only [runningMax, max_eq_left h] using heq
      · refine ⟨n + 1, le_rfl, ?_⟩
        simp only [runningMax, max_eq_right (by omega : runningMax U n ≤ U (n + 1))]















end ErdosProblems.Erdos243.PaperCompleteR11


