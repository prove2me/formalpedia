-- Prove2me | Theorems.Thm_preimage_insert
-- name    : preimage_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:47:40.956424+00:00
-- url     : https://prove2.me/theorems/40b9b55d-5531-4ff9-ab9f-89f3afbda1e2
-- title:
--   preimage insert: preimage insert
-- statement:
--   Restricting along an injection commutes with adding one event.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L96-L105
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean#L96-L105

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration
set_option autoImplicit true
variable {L : Type*} (es : PES L)

theorem preimage_insert {α β : Type*} {ι : α → β} (hι : Function.Injective ι)
    (c : Set β) (x : α) : {y | ι y ∈ c ∪ {ι x}} = {y | ι y ∈ c} ∪ {x} := by sorry
