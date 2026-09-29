-- Prove2me | Theorems.Thm_Erdos146_withoutReplacementBinaryPairMass_eq_pairTypeGroup
-- name    : Erdos146.withoutReplacementBinaryPairMass_eq_pairTypeGroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:45:58.671369+00:00
-- url     : https://prove2.me/theorems/53f6ceb6-d5bb-43b6-b00a-4bfbdbf1975c
-- title:
--   Without-replacement pair mass equals the type-group count (Lemma 5.2)
-- statement:
--   **Lemma 5.2 (Without-replacement correction).** Let $L \ge 4$ and $x_1,\dots,x_L \in \{0,1\}$, and sample an ordered pair of distinct indices uniformly. The resulting joint mass on parent bit pairs is exactly the normalised count of the corresponding type group. In the layered construction the two parents are sampled *without* replacement, and this identity is what lets the independent-sampling computation be used in its place.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L13516-L13544

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Choose.Cast

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.withoutReplacementBinaryPairMass_eq_pairTypeGroup
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    withoutReplacementBinaryPairMass parentCount
        (pairParentCoordinateOneCount parents coordinate) left right =
      ((pairTypeGroup parents coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
          (if left = right then (1 : ℝ) else 1 / 2) := by sorry
