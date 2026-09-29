-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_nested_finite_strip_decomposition
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.nested_finite_strip_decomposition
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T18:52:30.454511+00:00
-- url     : https://prove2.me/theorems/adb0d427-c7bf-4eb8-80d2-d3d60daac9c5
-- title:
--   Nested finite strip decomposition
-- statement:
--   A finite sum over nested sets decomposes exactly by first-entry strips, with each point's contributions beginning at its entry index.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/StripDecomposition.lean#L32-L54
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

theorem ErdosProblems.Erdos269.PaperCompleteR20.nested_finite_strip_decomposition {α : Type*} [DecidableEq α]
    (T : ℕ → Finset α) (hT : Monotone T) (F : ℕ → α → ℝ) (σ : ℕ) :
    (∑ ν ∈ Finset.range (σ + 1), ∑ x ∈ T ν, F ν x) =
      ∑ s ∈ Finset.range (σ + 1), ∑ x ∈ entryStrip T s,
        ∑ ν ∈ Finset.Icc s σ, F ν x := by sorry
