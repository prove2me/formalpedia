-- Prove2me | Theorems.Thm_isCompact_convexWeights
-- name    : isCompact_convexWeights
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:20:00.772441+00:00
-- url     : https://prove2.me/theorems/72d0657a-c503-530f-992c-51a10ad3681e
-- title:
--   is Compact convex Weights: is Compact convex Weights
-- statement:
--   **The weights of convex combinations form a compact set**: the vectors `w ∈ ℝᵏ` with
--   nonnegative entries summing to one.  It is closed, as an intersection of closed half-spaces
--   with a hyperplane, and bounded, since each entry lies in `[0, 1]`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/CompactConvexHull.lean#L36-L45
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/CompactConvexHull.lean#L36-L45

module
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_BasicResults_CompactConvexHull
set_option autoImplicit true
@[expose] public section
public section

theorem isCompact_convexWeights (k : ℕ) :
    IsCompact {w : Fin k → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by sorry
