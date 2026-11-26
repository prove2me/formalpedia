-- Prove2me | Theorems.Thm_bourbaki_witt_of_complete
-- name    : bourbaki_witt_of_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:46:29.548887+00:00
-- url     : https://prove2.me/theorems/0e2cab50-6298-5348-9342-64ef23e27a30
-- title:
--   bourbaki witt of complete: bourbaki witt of complete
-- statement:
--   The bourbaki witt of complete construction uses the bourbaki witt of complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L562-L572
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L562-L572

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
open ChainBounding

theorem bourbaki_witt_of_complete [CompletePartialOrder α] (g : α → α) (hg : ∀x, x ≤ g x) :
    ∃ x, g x = x := by sorry
