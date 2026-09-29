-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_GrowthRecordEquivalence_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_GrowthRecordEquivalence_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:48:34.155475+00:00
-- url     : https://prove2.me/theorems/21f25849-70cd-4cf6-96f7-710476271f80
-- title:
--   Canonical numerator ratio identity
-- statement:
--   Contains the exact source-proved identity relating the ratio of consecutive canonical numerators to the reciprocal-series and centered-error coordinates. The quadratic growth limit is supplied separately and is not proved by this bundle alone.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/GrowthRecordEquivalence.lean#L1-L333
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_GrowthRecordEquivalence_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.GrowthRecordEquivalence.

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

namespace ErdosProblems.Erdos243.PaperCompleteR9
end ErdosProblems.Erdos243.PaperCompleteR9

/-!
# The canonical weighted growth-defect criterion


This module supplies the previously missing `weightedgrowth` endpoint, not
merely a comparison conditional on a growth-budget supplier.  The error
budget is proved from the actual canonical reciprocal tail by the ratio
test: `(Cₙ₊₁/aₙ₊₁)/(Cₙ/aₙ) → 0`.  No subexponential estimate for C and no
unproved summability hypothesis are used.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter PaperCompleteR7 PaperCompleteR9
open scoped BigOperators Topology















/-- The real-tail quotient is the canonical integer-numerator quotient. -/
theorem canonical_numerator_ratio_eq
    (a : ℕ → ℕ) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (canonicalNaturalNumerator a p q (n + 1) : ℝ) /
        (canonicalNaturalNumerator a p q n : ℝ) =
      (a n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) /
        realTail (fun k ↦ 1 / (a k : ℝ)) n := by
  obtain ⟨hC, hD, _hnum, hden, hrep⟩ := canonical_integer_tail a hapos p q hq hs
  have hd0 : (canonicalDenominator a q n : ℝ) ≠ 0 := by exact_mod_cast (hD n).ne'
  have ht0 : realTail (fun k ↦ 1 / (a k : ℝ)) n ≠ 0 :=
    (realTail_pos _ hs.summable
      (fun k ↦ one_div_pos.mpr (by exact_mod_cast hapos k)) n).ne'
  rw [hrep (n + 1), hrep n, hden n, Nat.cast_mul]
  field_simp [hd0, ht0]
  <;> ring













end ErdosProblems.Erdos243.PaperCompleteR11


