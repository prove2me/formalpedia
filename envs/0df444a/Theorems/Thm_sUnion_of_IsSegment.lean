-- Prove2me | Theorems.Thm_sUnion_of_IsSegment
-- name    : sUnion_of_IsSegment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:32.91535+00:00
-- url     : https://prove2.me/theorems/2d77ab76-66db-5c05-bed5-b108bd8ff0ee
-- title:
--   s Union of Is Segment: s Union of Is Segment
-- statement:
--   The union of a family `F` of initial segments of a subset is an initial segment.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L123-L130
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L123-L130

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α]

theorem sUnion_of_IsSegment {F : Set (Set α)} (hF : ∀M ∈ F, M ⊑ C) : ⋃₀ F ⊑ C := by sorry
