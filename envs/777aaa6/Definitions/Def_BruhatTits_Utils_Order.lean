-- Prove2me | Definitions.Def_BruhatTits_Utils_Order
-- name    : BruhatTits_Utils_Order
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:40:31.565209+00:00
-- url     : https://prove2.me/theorems/dfd41df8-4ca6-4c23-8220-f407218aeae6
-- title:
--   Order
-- statement:
--   Definitions and structural lemmas for Order, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Order.lean

import Mathlib.Order.Hom.Basic
set_option autoImplicit false
variable {α β : Type*} [PartialOrder α] [PartialOrder β] (f : α ≃o β)


