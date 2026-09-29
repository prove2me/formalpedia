-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_InclusiveLimsup_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_InclusiveLimsup_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:57:14.932449+00:00
-- url     : https://prove2.me/theorems/d8d3e2d1-ffa5-453a-bba0-0ca583cfb5bd
-- title:
--   Negative-error log-log charge and record rate
-- statement:
--   For a natural sequence U, put H_n=max_(j≤n) U_j and ell(x)=log_2(log_2(max(4,x))). Defines the record charge (H_(n+1)-H_n)/ell(H_n), its extended-real limsup Theta(U), and the negative-error charge max(-E_n,0)/ell(U_n). The record and error charges use different height arguments, exactly as required by their separate comparison theorem.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/InclusiveLimsup.lean#L1-L142
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_InclusiveLimsup_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup.

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
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CoprimeCores_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_LogLogNormaliser_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_OrbitBlockArithmetic_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_PresievedCRT_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_RecordGcdReduction_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_InclusiveRecordAssembly_v243UnionFbf41fb8
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Extended-real inclusive log-log endpoint


The limsup is taken in EReal, so an unbounded quotient is not silently
replaced by a real conditionally-complete-lattice default. The normaliser
is the paper's exact log_2(log_2(max(4,x))). All-index true running-maximum
increments are used, exactly as in the definition of Theta in the paper.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter PaperCompleteR7
open scoped Topology



/-- The paper's all-index record quotient, before passing to a limsup. -/
noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)

/-- The exact extended-real record coefficient Theta. -/
noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop





/-- The error observable in the inclusive corollary. The negative part is
formed in integers first, and then cast into the ordinary real quotient. -/
noncomputable def negativeErrorLogLogCharge (U : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  ((max (-E n) 0 : ℤ) : ℝ) / recordLogLog (U n)









end ErdosProblems.Erdos243.PaperCompleteR11


