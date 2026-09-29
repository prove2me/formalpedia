-- Prove2me | solution 1 for ErdosProblems.Erdos269.reducedIntegralCarry_window
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:12:21.738533+00:00
-- url     : https://prove2.me/submissions/6cc3e374-6cbc-466a-abab-4bcd2650c4a5

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Theorems.Thm_ErdosProblems_Erdos269_integralCarry_cancel_commonFactor
import Theorems.Thm_ErdosProblems_Erdos269_integralCarry_window
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: restricted floor sums and local windows

Problem-owned landing surface for the exact true-shell floor sums and the
local-window residue reduction.  No declaration here asserts the open
cofinal anti-concentration theorem.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators

/-! ## Exact finite strict counts -/

















/-! ## Exact two-dimensional fiber formula -/







































/-! ## Generic logarithmic-window algebra -/



















/-! ## Exact denominator-factor cancellation -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (c d b m : ℕ → ℤ) (smoothFactor reducedDenominator : ℤ)
    (hsmooth : smoothFactor ≠ 0)
    (hfactor : ∀ n, c n = smoothFactor * d n)
    (hrec : ∀ n,
      c (n + 1) = b n * c n -
        (smoothFactor * reducedDenominator) * m n)
    (lo len : ℕ) :
    d (lo + len) =
      windowBase b lo len * d lo -
        reducedDenominator * windowForcing b m lo len := by
  exact integralCarry_window d b m reducedDenominator lo len
    (integralCarry_cancel_commonFactor c d b m smoothFactor
      reducedDenominator hsmooth hfactor hrec)
