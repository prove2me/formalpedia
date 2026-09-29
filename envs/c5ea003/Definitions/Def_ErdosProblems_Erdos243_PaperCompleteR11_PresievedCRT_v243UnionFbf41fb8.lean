-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_PresievedCRT_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_PresievedCRT_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:45:28.111984+00:00
-- url     : https://prove2.me/theorems/f5e814a8-27e8-4ee3-b524-5b6341da547b
-- title:
--   Admissible offsets for pre-sieved CRT
-- statement:
--   Defines the finite set of offsets coprime to an old modulus, used to assign pairwise-coprime new moduli only to admissible positions. Its totient cardinality and covering properties are separate theorem cards.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/PresievedCRT.lean#L1-L289
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_PresievedCRT_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.PresievedCRT.

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
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Exact finite pre-sieving and the primitive record fence


The modulus W is part of the CRT construction, not merely mentioned in
an offset-counting hypothesis.  Thus x is a multiple of W, and only the
phi(W)/W proportion of offsets coprime to W need individual old moduli.
The exact count, its asymptotic proportion, the bounded CRT phase and the
primitive first-crossing contradiction are all supplied here.  Selection
of the canonical moduli and the final log-log limit remain separate.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter
open scoped BigOperators Topology

/-- The offsets not already excluded by the old primitive denominator W. -/
def presievedOffsets (W B : ℕ) : Finset ℕ :=
  (Finset.range B).filter (fun r ↦ Nat.Coprime W r)



















end ErdosProblems.Erdos243.PaperCompleteR11


