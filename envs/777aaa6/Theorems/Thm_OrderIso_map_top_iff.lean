-- Prove2me | Theorems.Thm_OrderIso_map_top_iff
-- name    : OrderIso.map_top_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:00:39.195993+00:00
-- url     : https://prove2.me/theorems/aa5b1b18-056f-41f8-87ba-e32557395f08
-- title:
--   Order Iso: map top iff
-- statement:
--   The Order Iso construction uses the map top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Order.lean#L5-L8
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Order.lean#L5-L8

import Mathlib.Order.Hom.Basic
import Definitions.Def_BruhatTits_Utils_Order
set_option autoImplicit false
variable {α β : Type*} [PartialOrder α] [PartialOrder β] (f : α ≃o β)

theorem OrderIso.map_top_iff [OrderTop α] [OrderTop β] (x : α) :
    f x = ⊤ ↔ x = ⊤ := by sorry
