-- Prove2me | Theorems.Thm_OrderIso_map_bot_iff
-- name    : OrderIso.map_bot_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:00:46.79328+00:00
-- url     : https://prove2.me/theorems/36551c19-6d3a-44ed-a7c3-ab64a3c3bc9f
-- title:
--   Order Iso: map bot iff
-- statement:
--   The Order Iso construction uses the map bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Order.lean#L10-L13
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Order.lean#L10-L13

import Mathlib.Order.Hom.Basic
import Definitions.Def_BruhatTits_Utils_Order
set_option autoImplicit false
variable {α β : Type*} [PartialOrder α] [PartialOrder β] (f : α ≃o β)

theorem OrderIso.map_bot_iff [OrderBot α] [OrderBot β] (x : α) :
    f x = ⊥ ↔ x = ⊥ := by sorry
