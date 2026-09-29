-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_LcmCriticalBoundary
-- name    : ErdosProblems_Erdos243_LcmCriticalBoundary
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:26:59.443018+00:00
-- url     : https://prove2.me/theorems/822195d2-66ac-469a-a0e2-98b975b48bfb
-- title:
--   LCM block weights
-- statement:
--   Defines the finite block product W(g,r,0)=1 and W(g,r,k+1)=W(g,r,k)g_(r+k). The included zero and successor identities fix its indexing for the record-crossing argument.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmCriticalBoundary.lean#L1-L388
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_LcmCriticalBoundary is the versioned native alias of original module ErdosProblems.Erdos243.LcmCriticalBoundary.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

/-!
# Erdős 243: the LCM critical boundary

This module formalizes the strict-rise CRT consumer and weighted block
telescope arising from the LCM-cleared tail state.
-/

namespace ErdosProblems.Erdos243













/-- Multiplicative LCM weight on the first `k` steps after `r`. -/
def lcmBlockWeight (g : ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => lcmBlockWeight g r k * g (r + k)

@[simp]
theorem lcmBlockWeight_zero (g : ℕ → ℕ) (r : ℕ) :
    lcmBlockWeight g r 0 = 1 := rfl

@[simp]
theorem lcmBlockWeight_succ (g : ℕ → ℕ) (r k : ℕ) :
    lcmBlockWeight g r (k + 1) =
      lcmBlockWeight g r k * g (r + k) := rfl













end ErdosProblems.Erdos243


