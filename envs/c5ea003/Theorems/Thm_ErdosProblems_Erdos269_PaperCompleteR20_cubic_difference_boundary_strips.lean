-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_cubic_difference_boundary_strips
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.cubic_difference_boundary_strips
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:38:23.709857+00:00
-- url     : https://prove2.me/theorems/1a974e24-6557-4337-a4be-aa80eca5cda7
-- title:
--   Cubic difference boundary strips
-- statement:
--   A cubic finite difference of constant point weights on four nested finite sets is the signed sum of their three entry strips with coefficients -1, 2, -1.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/StripDecomposition.lean#L56-L67
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_StripDecomposition
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# First-entry strips in a nested finite family

A point contributes to every later set after its first appearance. This
finite identity separates cancellation in the common interior from the
three moving boundary strips of a cubic difference.
-/


open scoped BigOperators

open ErdosProblems.Erdos269.PaperCompleteR20

theorem ErdosProblems.Erdos269.PaperCompleteR20.cubic_difference_boundary_strips {α : Type*} [DecidableEq α]
    (T : ℕ → Finset α) (hT : Monotone T) (w : α → ℝ) :
    (∑ x ∈ T 0, w x) - 3 * (∑ x ∈ T 1, w x) +
        3 * (∑ x ∈ T 2, w x) - (∑ x ∈ T 3, w x) =
      -(∑ x ∈ T 1 \ T 0, w x) + 2 * (∑ x ∈ T 2 \ T 1, w x) -
        (∑ x ∈ T 3 \ T 2, w x) := by sorry
