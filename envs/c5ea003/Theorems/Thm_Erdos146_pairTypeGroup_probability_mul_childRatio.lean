-- Prove2me | Theorems.Thm_Erdos146_pairTypeGroup_probability_mul_childRatio
-- name    : Erdos146.pairTypeGroup_probability_mul_childRatio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:45:46.233047+00:00
-- url     : https://prove2.me/theorems/4731819c-18e1-43c9-a978-a3197f5f3b97
-- title:
--   Type-group probability times the child ratio
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. The product of a type group's probability with its child ratio, in the form used to assemble the empirical conditional entropy.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L13486-L13514

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairTypeGroup_probability_mul_childRatio
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
        ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroupChildOnes parents children
        coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by sorry
