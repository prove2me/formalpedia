-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_integralCarry_cancel_commonFactor
-- name    : ErdosProblems.Erdos269.integralCarry_cancel_commonFactor
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:58:21.291541+00:00
-- url     : https://prove2.me/theorems/1b4f84db-b8fb-4599-8319-3979fa06be19
-- title:
--   IntegralCarry cancel commonFactor
-- statement:
--   A nonzero common factor can be cancelled from every state of an integer carry recurrence.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L577-L596
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
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


open scoped BigOperators

/-! ## Exact finite strict counts -/

















/-! ## Exact two-dimensional fiber formula -/







































/-! ## Generic logarithmic-window algebra -/



















/-! ## Exact denominator-factor cancellation -/

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.integralCarry_cancel_commonFactor
    (c d b m : ℕ → ℤ) (smoothFactor reducedDenominator : ℤ)
    (hsmooth : smoothFactor ≠ 0)
    (hfactor : ∀ n, c n = smoothFactor * d n)
    (hrec : ∀ n,
      c (n + 1) = b n * c n -
        (smoothFactor * reducedDenominator) * m n) :
    ∀ n, d (n + 1) = b n * d n - reducedDenominator * m n := by sorry
