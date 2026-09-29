-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_LcmRecordDivergence
-- name    : ErdosProblems_Erdos243_LcmRecordDivergence
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:28:35.359679+00:00
-- url     : https://prove2.me/theorems/6592c744-b29d-42f1-bf6e-9dfc1c5684bb
-- title:
--   Record excess weight
-- statement:
--   For U:N→N, B:N and f:N→R, defines a charge at step n to be max(U_(n+1)-U_n-B,0) f(U_n) if U_(n+1)>U_j for every j≤n, and zero otherwise. The definition permits any real-valued f; nonnegativity and divergence conditions are hypotheses of the separate theorems.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordDivergence.lean#L1-L59
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_LcmRecordDivergence is the versioned native alias of original module ErdosProblems.Erdos243.LcmRecordDivergence.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

/-!
# From finite first crossings to divergent record mass

This module transfers nonsummability of the actual progression weights to
the record-excess series. The sequence need only reach arbitrarily large
heights; no monotonicity or limit at infinity is assumed. The analytic input
that a particular weight has divergent progression sum remains explicit.
-/

namespace ErdosProblems.Erdos243.LcmRecordCrossing

/-- The nonnegative charge at a strict record, zero at every other step. -/
noncomputable def recordExcessWeight (U : ℕ → ℕ) (B : ℕ) (f : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  if (∀ j ≤ n, U j < U (n + 1)) then
    ((U (n + 1) - U n - B : ℕ) : ℝ) * f (U n) else 0



end ErdosProblems.Erdos243.LcmRecordCrossing


