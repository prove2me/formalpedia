-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_ProductDefect_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR7_ProductDefect_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:46:41.46136+00:00
-- url     : https://prove2.me/theorems/c74ae04f-badf-4207-ab38-f121733dd0f5
-- title:
--   Real product-prefactor defect
-- statement:
--   Defines the real expression (P_n/a_n)(a_n^2/a_(n+1)−1), where P_n is the prefix product of the digits. It is a real analytic defect, not an integer centered error; the endpoint implication from its boundedness is a separate theorem.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR7/ProductDefect.lean#L1-L249
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR7_ProductDefect_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The original-coordinate bounded-product-defect corollary

Compiled candidates.  This module supplies the analytic error dictionary
rather than assuming bounded centred error.  Finite upper limsup is stated
as eventual boundedness above by a real constant; the finite initial
segment is irrelevant.  Rationality is given by p/q and HasSum.

The proof avoids assuming a pre-existing double-exponential estimate:
P_n/a_n^2 tends to zero by its successive-ratio identity.  This suffices
for the exact two-term error dictionary.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators

noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)











end ErdosProblems.Erdos243.PaperCompleteR7


