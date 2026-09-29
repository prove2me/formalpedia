-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_conditional_denominator_reduction_real_bound
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.conditional_denominator_reduction_real_bound
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:59:31.668934+00:00
-- url     : https://prove2.me/theorems/4532d3b4-7138-40a9-8598-0f367d032a35
-- title:
--   Conditional denominator reduction real bound
-- statement:
--   Suppose an integer carry c is a positive common factor s times an integer carry d, and c obeys the scaled digit recurrence. Then d obeys the unscaled recurrence and every finite-window formula. At each index, positivity and an upper bound on c by sB times any real t are equivalent to the corresponding positivity and bound on d by B times t.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/RealBoundDenominatorReduction.lean#L23-L37
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
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ErdosProblems.Erdos269.PaperCompleteR20
end ErdosProblems.Erdos269.PaperCompleteR20

/-!
# Denominator reduction with the literal real upper bound

The paper quantifies the upper-bound parameter over all reals and asserts an
equivalence. Positive common-factor cancellation preserves both directions;
no integrality of that parameter or bound function is needed.
-/

open ErdosProblems.Erdos269.PaperCompleteR20

theorem ErdosProblems.Erdos269.PaperCompleteR20.conditional_denominator_reduction_real_bound
    (c d b m : ℕ → ℤ) (s B : ℤ) (hs : 0 < s)
    (hfactor : ∀ n, c n = s * d n)
    (hrec : ∀ n, c (n + 1) = b n * c n - (s * B) * m n) :
    (∀ n, d (n + 1) = b n * d n - B * m n) ∧
    (∀ lo len, d (lo + len) = windowBase b lo len * d lo -
      B * windowForcing b m lo len) ∧
    (∀ n (t : ℝ),
      (0 < c n ∧ (c n : ℝ) ≤ ((s * B : ℤ) : ℝ) * t) ↔
        (0 < d n ∧ (d n : ℝ) ≤ (B : ℝ) * t)) := by sorry
