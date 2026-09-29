-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CoprimeCores_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_CoprimeCores_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:45:41.187747+00:00
-- url     : https://prove2.me/theorems/a8909057-1f3c-44dd-9ad6-56d780808ed1
-- title:
--   Coprime cores of overlapping multipliers
-- statement:
--   For positive indexed natural multipliers A_i, defines coreDenom(A,i)=gcd(A_i, ∏_(j≠i)A_j) and coprimeCore(A,i)=A_i/coreDenom(A,i) by natural division. Included identities establish exact factorization and pairwise coprimality of the cores; quantitative loss from bounded original pairwise gcds is a separate theorem card.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/CoprimeCores.lean#L1-L189
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_CoprimeCores_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.CoprimeCores.

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
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Coprime cores of a finite non-coprime family

Removing gcd(A_i, product of all other A_j) yields pairwise-coprime
cores. The loss is bounded by the product of the pairwise gcds. This avoids
an unproved supply of pairwise-coprime original multipliers in the
non-stabilised-gcd branch of the inclusive argument.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators





noncomputable def coreDenom {B : ℕ} (A : Fin B → ℕ) (i : Fin B) : ℕ :=
  Nat.gcd (A i) (∏ j ∈ Finset.univ.erase i, A j)

noncomputable def coprimeCore {B : ℕ} (A : Fin B → ℕ) (i : Fin B) : ℕ :=
  A i / coreDenom A i















end ErdosProblems.Erdos243.PaperCompleteR11


