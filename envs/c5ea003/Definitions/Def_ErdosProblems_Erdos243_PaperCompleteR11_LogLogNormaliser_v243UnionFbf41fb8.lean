-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_LogLogNormaliser_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_LogLogNormaliser_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:50:36.549182+00:00
-- url     : https://prove2.me/theorems/d9fbc00a-e7f7-4051-aadf-1f877ddbbd24
-- title:
--   Binary tower and record log-log normaliser
-- statement:
--   Defines the binary tower T_n=2^(2^n) and the real height scale ell(x)=log_2(log_2(max(4,x))). Included elementary power and tower identities support later quantitative estimates; the cutoff keeps the logarithmic denominator positive at small heights.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/LogLogNormaliser.lean#L1-L116
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_LogLogNormaliser_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_GlobalLcmHeight
import Definitions.Def_ErdosProblems_Erdos243_CumulativeLcmTransfer
import Definitions.Def_ErdosProblems_Erdos243_LcmCriticalBoundary
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PrimitiveRecordBarrier
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_RecordDivisibility_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_ProductDefect_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_LcmDefect_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_GrowthRecordEquivalence_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CanonicalGrowthBounds_v243UnionFbf41fb8
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
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
# Exact base-two log-log normalisation


The cut-off is exactly `max 4 x`, as in the paper. The tower identities
are exact, including the normalisation constant: no change of logarithm
base is absorbed into an unspecified asymptotic constant.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- An integer height which the paper's normaliser sends to its index. -/
def binaryTower (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/-- An elementary exponent estimate, including the index zero. -/
theorem index_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

/-- Monotonicity in a natural exponent, proved without an asymptotic API. -/
theorem two_pow_mono {n m : ℕ} (h : n ≤ m) : 2 ^ n ≤ 2 ^ m :=
  Nat.pow_le_pow_right (by norm_num) h









/-- The exact real-valued normaliser from the inclusive boundary. -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2

















end ErdosProblems.Erdos243.PaperCompleteR11


