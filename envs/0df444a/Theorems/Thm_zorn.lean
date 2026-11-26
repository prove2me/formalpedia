-- Prove2me | Theorems.Thm_zorn
-- name    : zorn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:46:10.760218+00:00
-- url     : https://prove2.me/theorems/25608df0-60c6-571c-9770-bc73ff4a7e64
-- title:
--   zorn: zorn
-- statement:
--   The zorn construction uses the zorn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L547-L556
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L547-L556

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open ChainBounding

theorem zorn [PartialOrder α] [Inhabited α]
    (ind : ∀ (C : Set α), IsChain (· ≤ ·) C → ∃ ub, ∀ a ∈ C, a ≤ ub) : ∃ (x : α), IsMaximal x := by sorry
