-- Prove2me | Theorems.Thm_unbounded_chain
-- name    : unbounded_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:46:08.746912+00:00
-- url     : https://prove2.me/theorems/2c45fdff-c316-4a32-bef7-51545f26d99a
-- title:
--   unbounded chain: unbounded chain
-- statement:
--   Every poset has a chain without strict upper bounds.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L533-L538
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L533-L538

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open ChainBounding

theorem unbounded_chain [PartialOrder α] [Inhabited α] :
    ∃ C, IsChain (· ≤ ·) C ∧ ¬ ∃ sb : α, ∀ a ∈ C, a < sb := by sorry
