-- Prove2me | Theorems.Thm_exists_strictBound_of_IsSegment
-- name    : exists_strictBound_of_IsSegment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:45:35.427808+00:00
-- url     : https://prove2.me/theorems/cf1255f6-e965-5bf3-b1af-5b101effbca9
-- title:
--   exists strict Bound of Is Segment: exists strict Bound of Is Segment
-- statement:
--   A proper initial segment of a chain has an strict upper bound in the chain.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L135-L148
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L135-L148

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α]

theorem exists_strictBound_of_IsSegment (S C : Set α) (hSC : S ⊏ C) (cha : IsChain (· ≤ ·) C) :
    ∃ sb ∈ C, ∀ a ∈ S, a < sb := by sorry
