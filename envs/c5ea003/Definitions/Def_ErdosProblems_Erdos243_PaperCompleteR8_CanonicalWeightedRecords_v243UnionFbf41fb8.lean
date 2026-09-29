-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR8_CanonicalWeightedRecords_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR8_CanonicalWeightedRecords_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:48:43.692238+00:00
-- url     : https://prove2.me/theorems/d133f664-8b29-46db-a446-c2956a6b74f3
-- title:
--   Canonical LCM orbit
-- statement:
--   Defines the canonical LCM orbit constructed from a strictly increasing positive sequence with rational reciprocal sum and quadratic-ratio limit. The source construction carries exact integer coordinates; the weighted-record equivalence is a separate theorem.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR8/CanonicalWeightedRecords.lean#L1-L294
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR8_CanonicalWeightedRecords_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR8.CanonicalWeightedRecords.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_GlobalLcmHeight
import Definitions.Def_ErdosProblems_Erdos243_CumulativeLcmTransfer
import Definitions.Def_ErdosProblems_Erdos243_LcmCriticalBoundary
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordDivergence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PrimitiveRecordBarrier
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_ProductDefect_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_LcmDefect_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR8_WeightAnalysis_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR8_WeightedRecords_v243UnionFbf41fb8
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The canonical weighted-record equivalence

Complete compiled candidates for both occurrences of `res:weightedrecord`.
The rational value is supplied as `HasSum ... (p/q)`, exactly as in the
repaired r7 canonical-state theorem. All tail integrality and small-error
facts come from that theorem; none are additional hypotheses here.

The eventual-centred arithmetic theorem is obtained by shifting at a genuine
running maximum. Shifting at an arbitrary index would change the record set.
The converse implication uses the exact squared-error transport on a
Sylvester tail, rather than presuming zero error from the recurrence.

Mathlib facts used for casts and products also occur in the repaired r7
`LcmDefect.lean`: Int.natAbs_mul, Int.natAbs_natCast,
Nat.mul_lt_mul_left. All substantial arithmetic imports are supplied sources.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR8

open Filter Classical
open scoped BigOperators







/-- The exact canonical LCM state. Its data are definitions; its validity
proof reuses r7's compiled denominator-clearing theorem. -/
noncomputable def canonicalLcmOrbit
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (nhds 1)) :
    LcmOrbit := by
  let C := PaperCompleteR7.canonicalNaturalNumerator a p q
  let D := PaperCompleteR7.canonicalDenominator a q
  refine {
    a := a
    L := cumulativeDigitLcm q a
    U := lcmLiftedNumerator q a C
    V := lcmLiftedDigit q a C
    apos := hapos
    Lpos := cumulativeDigitLcm_pos hq hapos
    Upos := ?_
    nextL := fun _ => rfl
    step := ?_
    digit := fun _ => rfl
  }
  · obtain ⟨hCp, _, hC, _, _, _, _⟩ :=
      PaperCompleteR7.canonical_integer_tail_normalized a ha hapos p q hq hs hg
    have hscale : ∀ n, D n = digitProductScale q a n :=
      fun n => (PaperCompleteR7.productScale_eq_canonicalDenominator q a n).symm
    intro n
    have heq := lcmLiftedNumerator_spec q a C D hscale hC n
    by_contra hn
    have hz : lcmLiftedNumerator q a C n = 0 := by omega
    rw [hz, mul_zero] at heq
    exact (hCp n).ne' heq.symm
  · obtain ⟨_, _, hC, _, _, _, _⟩ :=
      PaperCompleteR7.canonical_integer_tail_normalized a ha hapos p q hq hs hg
    have hscale : ∀ n, D n = digitProductScale q a n :=
      fun n => (PaperCompleteR7.productScale_eq_canonicalDenominator q a n).symm
    exact lcmLifted_step C D hq hapos hscale hC







end ErdosProblems.Erdos243.PaperCompleteR8


